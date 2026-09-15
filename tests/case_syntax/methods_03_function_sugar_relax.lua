-- Assignment-to-method syntax is retained as plain field syntax without explicit provenance.
-- unluac: expect-contains [[.capture_root(p]]
-- receiver 的独立根不能因缩写调用而删除；源码本身也是普通点调用。
-- unluac: expect-contains [[.effectful_relaxed(]]
-- unluac: expect-contains [[:direct_statement_only()]]
-- 数值计数器也会写原槽；终端调用须保留唯一 local，后继 GC 固定其覆盖责任。
-- unluac: expect-ast-count [[local-decl]] [[1]] [[@proto=19]] [[@dialect=lua5.4]]

local root_object = {}
root_object.capture_root = function(receiver, value)
    return receiver == root_object and value
end

assert(root_object:capture_root(37) == 37)

local effect_count = 0
local method_owner = {}
function method_owner:effectful_relaxed(value)
    return value
end

local function make_method_owner()
    effect_count = effect_count + 1
    return method_owner
end

local function call_effectful_receiver()
    local effect_receiver = make_method_owner()
    return effect_receiver.effectful_relaxed(effect_receiver, 43)
end

local effect_result = call_effectful_receiver()
assert(effect_result == 43 and effect_count == 1)

-- A direct call statement has the same two-use receiver snapshot as an assigned call.
local direct_call_count = 0
local function make_direct_call_receiver()
    direct_call_count = direct_call_count + 1
    return {
        direct_statement_only = function(self)
            direct_call_count = direct_call_count + 1
        end,
    }
end
local function call_direct_receiver()
    local direct_receiver = make_direct_call_receiver()
    direct_receiver.direct_statement_only(direct_receiver)
end

call_direct_receiver()
assert(direct_call_count == 2)

-- A write target is not a read use; removing its alias declaration would retarget the write.
local write_target_receiver = {
    touch = function(self)
        return "inner"
    end,
}
local receiver = "outer"
local observed_receiver = "unset"
local function write_target_probe(flag)
    local receiver = flag and write_target_receiver
    receiver = receiver.touch(receiver)
    observed_receiver = receiver
    return receiver
end
assert(write_target_probe(true) == "inner")
assert(receiver == "outer")
assert(observed_receiver == "inner")
assert(write_target_receiver.touch(write_target_receiver) == "inner")

-- Forwarding one closure to multiple sinks must preserve one shared object and its local owner.
local shared_forward_owner = {}
local shared_forwarded = function()
    return 47
end
shared_forward_owner.first = shared_forwarded
shared_forward_owner.second = shared_forwarded
assert(shared_forward_owner.first == shared_forward_owner.second)
assert(shared_forward_owner.first() == 47)

local constructor_events = {}
local function mark(name)
    constructor_events[#constructor_events + 1] = name
    return name
end

local function consume(outer, middle)
    return outer.child.tag, middle
end

local function build_constructor()
    local callee = consume
    local outer = { tag = mark("outer") }
    local middle = mark("middle")
    local inner = { tag = mark("inner") }
    outer.child = inner
    return callee(outer, middle)
end

local inner_tag, middle_tag = build_constructor()
assert(inner_tag == "inner" and middle_tag == "middle")
assert(table.concat(constructor_events, ",") == "outer,middle,inner")

local original_assert, original_print = assert, print
local terminal_weak = setmetatable({}, {__mode = "v"})
local terminal_seen, terminal_seen_second
local observation_gate = setmetatable({}, {__index = function()
    collectgarbage("collect")
    terminal_seen = terminal_weak[1] ~= nil
    terminal_seen_second = terminal_weak[2] ~= nil
    return false
end})
local function observed_assert(value)
    local ignored = observation_gate.trigger
    -- 保留 lookup 调用帧的宽度，不能让元方法准备区先覆盖待观察的原槽。
    local a, b, c = false, false, false
    return original_assert(value)
end
local function seed_print(label, inner, middle)
    -- 三个形参后的第三个槽，与下方终端返回闭包的原写槽相同。
    local a, b, resource, following = false, false, {}, {}
    terminal_weak[1] = resource
    -- 相邻高槽应继续保活，防止多出的 callee 声明把整个调用帧向上推一槽。
    terminal_weak[2] = following
    original_print(label, inner, middle)
end
collectgarbage("stop")
seed_print("function-sugar-relax", inner_tag, middle_tag)

local terminal_callee_events = 0
local function make_terminal_callee()
    terminal_callee_events = terminal_callee_events + 1
    return function()
        terminal_callee_events = terminal_callee_events + 1
    end
end

local function call_terminal_callee()
    local terminal_callee = make_terminal_callee()
    terminal_callee()
end

call_terminal_callee()
observed_assert(terminal_callee_events == 2)
assert(terminal_seen == false and terminal_seen_second == true)
collectgarbage("restart")

-- 调用糖不能删除仍在使用的 receiver 根。
local receiver_weak = setmetatable({}, {__mode = "v"})
local function make_retained_receiver()
    local object = setmetatable({}, {__index = function(_, key)
        assert(key == "retained_receiver")
        collectgarbage("collect")
        assert(type(receiver_weak[1]) == "table")
        return function(self)
            collectgarbage("collect")
            assert(receiver_weak[1] == self)
            return 53
        end
    end})
    receiver_weak[1] = object
    return object
end
local retained_receiver = make_retained_receiver()
assert(retained_receiver.retained_receiver(retained_receiver) == 53)
collectgarbage("collect")
assert(receiver_weak[1] == retained_receiver)

-- 字段 lookup 可通过捕获改写 receiver；此时第二次读取必须取得新对象。
local changed_receiver
local replacement_receiver = {}
changed_receiver = setmetatable({}, {__index = function()
    changed_receiver = replacement_receiver
    return function(self)
        assert(self == replacement_receiver)
        return 59
    end
end})
assert(changed_receiver.lookup_rebind(changed_receiver) == 59)

-- 两侧 lookup 仍按原顺序求值，左侧元方法写回的 cell 必须被右侧观察到。
do
    local order = {}
    local current, expected = {}, {}
    local left = setmetatable({}, {__index = function()
        order[#order + 1] = "left"
        current = expected
        return expected
    end})
    local right = setmetatable({}, {__index = function()
        order[#order + 1] = "right"
        return current
    end})
    assert(left.value == right.value)
    assert(table.concat(order, ",") == "left,right")
end
