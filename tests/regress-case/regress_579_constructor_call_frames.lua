-- 原 constructor 批次与接收 CALL 必须作为完整槽序事务恢复。
-- GC 观察使用当前方言的源码输出作基线，不假定不同 VM 的栈扫描范围相同。
-- unluac: expect-not-contains [[unluac error]]
-- unluac: expect-not-contains [[table-set-list]]

local function open_widths()
    local function tail(many)
        if many then return "tail", nil, "last" end
    end
    local function receive(values)
        assert(values[1] == "first" and values[2] == nil)
        return values
    end
    local empty = receive({"first", nil, tail(false)})
    local many = receive({"first", nil, tail(true)})
    assert(empty[3] == nil and empty[4] == nil)
    assert(many[3] == "tail" and many[4] == nil and many[5] == "last")
    print("open-widths", #empty, #many, empty[3], many[3], many[4], many[5])
end

local function record_order()
    local events = {}
    local function record(event)
        events[#events + 1] = event
    end
    local operand = setmetatable({}, {__mul = function(_, factor)
        record("mul")
        collectgarbage("collect")
        return {value = factor * 4}
    end})
    local target = setmetatable({}, {__index = function(_, key)
        assert(key == "w")
        record("target.w")
        return operand
    end})
    local operations = setmetatable({}, {__index = function(_, key)
        record("lookup-" .. key)
        return function(value)
            record("call-" .. key)
            return value
        end
    end})
    local first = {first = true}
    local result = operations.queue({
        first,
        operations.ease({
            rate = 1,
            interval = operations.move({target = target, duration = 300, x = target.w * 1.5}),
        }),
    })
    assert(result[1] == first and result[2].interval.x.value == 6)
    assert(table.concat(events, ",") ==
        "lookup-queue,lookup-ease,lookup-move,target.w,mul,call-move,call-ease,call-queue")
    print("record-order", table.concat(events, ","), result[2].interval.x.value)
end

local function callee_snapshot()
    local events = {}
    local current = function(values)
        events[#events + 1] = "old-receiver"
        assert(values[1] == 4 and values[2] == 5 and values[3] == 6)
        return #values
    end
    local source = setmetatable({}, {__index = function(_, key)
        assert(key == "receive")
        events[#events + 1] = "receiver-lookup"
        return current
    end})
    local function first()
        events[#events + 1] = "first"
        current = function() error("callee read after argument callback") end
        return 4
    end
    local function tail()
        events[#events + 1] = "tail"
        return 5, 6
    end
    local result = source.receive({first(), tail()})
    assert(result == 3)
    assert(table.concat(events, ",") == "receiver-lookup,first,tail,old-receiver")
    print("callee-snapshot", result, table.concat(events, ","))
end

local function dispatch_roots()
    local weak = setmetatable({}, {__mode = "v"})
    local function resource(key)
        local value = {}
        weak[key] = value
        return value
    end
    local function tail()
        return resource("tail"), nil
    end
    local function collect(label)
        collectgarbage("collect")
        collectgarbage("collect")
        print(label, type(weak.first), type(weak.middle), type(weak.tail), type(weak.seed))
    end
    local function receive(values)
        weak.seed = values
        assert(values[1] == weak.first and values[2] == weak.middle and values[3] == weak.tail)
        values[1], values[2], values[3] = nil, nil, nil
        collect("inside-receiver")
        return 37
    end
    local target = setmetatable({}, {__newindex = function(_, key, value)
        assert(key == "state" and value == 37)
        collect("after-receiver")
    end})
    local function build()
        -- first 的低槽根独立存活，批次 COPY 不能代替它；另两个原结果槽在 dispatch 退休。
        local first = resource("first")
        local unrelated = receive({first, resource("middle"), tail()})
        target.state = unrelated
        return first
    end
    collectgarbage("stop")
    local kept = build()
    assert(kept == weak.first)
    collect("after-build")
    collectgarbage("restart")
end

local function previous_activation()
    local weak = setmetatable({}, {__mode = "v"})
    local observed
    local function stash()
        local marker = {}
        weak.previous = marker
        return 7, marker
    end
    local function tail()
        collectgarbage("collect")
        collectgarbage("collect")
        observed = type(weak.previous)
        return "tail"
    end
    local function receive(values)
        assert(values[1] == nil and values[2] == nil and values[3] == "tail")
        return values[3]
    end
    local function run()
        stash()
        return receive({nil, nil, tail()})
    end
    collectgarbage("stop")
    assert(run() == "tail")
    print("previous-activation", observed)
    collectgarbage("restart")
end

open_widths()
record_order()
callee_snapshot()
dispatch_roots()
previous_activation()

-- record 值的低寄存器读取不发 COPY；不能仅因内联结果不是 literal，就把原
-- scratch 写当作仍会发生。后续 __index 在写回同一 scratch 前能观察旧槽残值。
local function record_copy_slot()
    local weak = setmetatable({}, {__mode = "v"})
    local seen
    local function stash()
        local marker = {}
        weak.marker = marker
        return marker, 7
    end
    local function build(x, flag, receive, methods)
        stash()
        return receive({k = flag and x or x, q = methods.observe()})
    end
    local methods = setmetatable({}, {__index = function()
        collectgarbage("collect")
        collectgarbage("collect")
        seen = type(weak.marker)
        return function() return 1 end
    end})
    collectgarbage("stop")
    build({}, true, function(value) return value end, methods)
    print("record-copy-slot", seen)
    collectgarbage("restart")
end
record_copy_slot()

-- __call 会覆写原 callee 本槽；Ignore CALL 后留下的函数没有普通结果 Def。
-- 后续参数 COPY 仍须覆写这个槽，不能因原 callee 是数字就把旧值判为 GC-inert。
local function callable_number_slot()
    local weak = setmetatable({}, {__mode = "v"})
    local meta = {}
    meta.__call = function() meta.__call = nil end
    weak.fn = meta.__call
    local original = debug.getmetatable(1)
    debug.setmetatable(1, meta)
    local seen
    local methods = setmetatable({}, {__index = function()
        collectgarbage("collect")
        collectgarbage("collect")
        seen = type(weak.fn)
        return function(value) return value end
    end})
    local function build(x, receiver)
        (1)()
        local saved = x
        receiver.observe(saved)
    end
    collectgarbage("stop")
    build({}, methods)
    debug.setmetatable(1, original)
    print("callable-number-slot", seen)
    collectgarbage("restart")
end
callable_number_slot()

-- 只有 then 路径执行 CALL；合流处的 scratch 事实必须取 may-union，不能被未污染的
-- else 路径清空。两个实际调用都走同一 COPY/GETTABLE 后缀，不清空 weak 来掩盖残值。
local function branch_scratch_union()
    local weak = setmetatable({}, {__mode = "v"})
    local seen
    local function stash()
        local marker = {}
        weak.marker = marker
        return marker, 7
    end
    local function build(x, pollute, receive, methods)
        if pollute then stash() end
        return receive({k = pollute and x or x, q = methods.observe()})
    end
    local methods = setmetatable({}, {__index = function()
        collectgarbage("collect")
        collectgarbage("collect")
        seen = type(weak.marker)
        return function() return 1 end
    end})
    local function receive(values)
        return values
    end
    collectgarbage("stop")
    build({}, false, receive, methods)
    print("branch-scratch-union", false, seen)
    build({}, true, receive, methods)
    print("branch-scratch-union", true, seen)
    collectgarbage("restart")
end
branch_scratch_union()
