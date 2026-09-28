-- regress_337: fixed call results may be nil, so raw SETLIST must not be split into SETTABLE.
-- unluac: expect-ast-count [[table-list-field]] [[16]]
-- unluac: expect-ast-count [[table-record-field]] [[0]] [[@proto=10]] [[@dialect=luajit]]
-- unluac: expect-ast-count [[table-constructor]] [[1]] [[@proto=10]] [[@dialect=luajit]]
-- unluac: expect-ast-count [[table-record-field]] [[0]] [[@proto=11]] [[@dialect=luajit]]
-- unluac: expect-ast-count [[table-constructor]] [[1]] [[@proto=11]] [[@dialect=luajit]]
-- unluac: expect-ast-count [[table-record-field]] [[0]] [[@proto=3]] [[@dialect=luau]]
-- unluac: expect-ast-count [[table-constructor]] [[1]] [[@proto=3]] [[@dialect=luau]]
-- unluac: expect-ast-count [[table-record-field]] [[0]] [[@proto=1]] [[@dialect=luau]]
-- unluac: expect-ast-count [[table-constructor]] [[1]] [[@proto=1]] [[@dialect=luau]]
-- unluac: expect-ast-count [[table-record-field]] [[0]] [[@proto=3]] [[@dialect=lua5.5]]
-- unluac: expect-ast-count [[table-constructor]] [[1]] [[@proto=3]] [[@dialect=lua5.5]]
-- unluac: expect-ast-count [[table-record-field]] [[0]] [[@proto=1]] [[@dialect=lua5.5]]
-- unluac: expect-ast-count [[table-constructor]] [[1]] [[@proto=1]] [[@dialect=lua5.5]]
-- unluac: expect-ast-count [[table-record-field]] [[0]] [[@proto=3]] [[@dialect=lua5.4]]
-- unluac: expect-ast-count [[table-constructor]] [[1]] [[@proto=3]] [[@dialect=lua5.4]]
-- unluac: expect-ast-count [[table-record-field]] [[0]] [[@proto=1]] [[@dialect=lua5.4]]
-- unluac: expect-ast-count [[table-constructor]] [[1]] [[@proto=1]] [[@dialect=lua5.4]]
-- unluac: expect-ast-count [[table-record-field]] [[0]] [[@proto=3]] [[@dialect=lua5.3]]
-- unluac: expect-ast-count [[table-constructor]] [[1]] [[@proto=3]] [[@dialect=lua5.3]]
-- unluac: expect-ast-count [[table-record-field]] [[0]] [[@proto=1]] [[@dialect=lua5.3]]
-- unluac: expect-ast-count [[table-constructor]] [[1]] [[@proto=1]] [[@dialect=lua5.3]]
-- unluac: expect-ast-count [[table-record-field]] [[0]] [[@proto=3]] [[@dialect=lua5.2]]
-- unluac: expect-ast-count [[table-constructor]] [[1]] [[@proto=3]] [[@dialect=lua5.2]]
-- unluac: expect-ast-count [[table-record-field]] [[0]] [[@proto=1]] [[@dialect=lua5.2]]
-- unluac: expect-ast-count [[table-constructor]] [[1]] [[@proto=1]] [[@dialect=lua5.2]]
-- unluac: expect-ast-count [[table-record-field]] [[0]] [[@proto=3]] [[@dialect=lua5.1]]
-- unluac: expect-ast-count [[table-constructor]] [[1]] [[@proto=3]] [[@dialect=lua5.1]]
-- unluac: expect-ast-count [[table-record-field]] [[0]] [[@proto=1]] [[@dialect=lua5.1]]
-- unluac: expect-ast-count [[table-constructor]] [[1]] [[@proto=1]] [[@dialect=lua5.1]]

local function run()
    local calls = 0
    local function maybe_nil()
        calls = calls + 1
        return nil
    end

    local values = { "head", (maybe_nil()), "tail" }
    assert(calls == 1 and values[1] == "head" and values[2] == nil and values[3] == "tail")
    print("regress_337#nil-shape", calls, #values, values[1], values[2], values[3])
end

-- LuaJIT 的模板容量在首次序列化时归一化；两条基线都执行已加载的 chunk，
-- 保留 #table 的真实观察，而不把 source 编译器的内存模板当成字节码运行基线。
if jit then
    run = assert(loadstring(string.dump(run)))
end
run()

-- 条件结果在分支体内仍被读取，不能消费为条件表达式；该拒绝也不能阻断
-- 后续独立的 SETLIST 事务。分别观察分支未进入、结果为 nil 和正常对象三条路径。
-- unluac: expect-not-contains [[table-set-list]]
-- unluac: expect-not-contains [[unluac error]]
local function build_after_branch(self, flag)
    if flag then
        local child = self:getChild("before")
        if child then child.image = "changed" end
    end
    local first = self:getChild("one")
    local second = self:getChild("two")
    local third = self:getChild("three")
    self.list = { first, second, third }
end

for scenario = 1, 3 do
    local events = {}
    local child = {}
    local first = {}
    local owner = {}
    function owner:getChild(key)
        events[#events + 1] = key
        if key == "before" then
            if scenario == 2 then return nil end
            return child
        end
        if key == "one" then return first, "extra" end
        if key == "two" then return nil, "extra" end
        return false, "extra"
    end
    build_after_branch(owner, scenario ~= 1)
    assert(owner.list[1] == first and owner.list[2] == nil and owner.list[3] == false)
    assert(owner.list[4] == nil)
    assert(child.image == (scenario == 3 and "changed" or nil))
    local expected = scenario == 1 and "one,two,three" or "before,one,two,three"
    assert(table.concat(events, ",") == expected)
    print("branch before constructor", scenario, expected, child.image)
end

-- unluac: expect-contains [[function LayoutA.create()]] [[@dialect=luau]]
-- unluac: expect-contains [[function LayoutB.create()]] [[@dialect=luau]]
-- 连续发布字段与方法会复用匿名槽；数组中的全局索引仍应在原缓冲槽求值，
-- 不能把它误当成低槽 local 读取，进而阻断后继 SETLIST 的完整事务。
do
    local saved_events, saved_a, saved_b = events, LayoutA, LayoutB
    local trace = ""
    events = setmetatable({}, { __index = function(_, key)
        trace = trace .. key
        return key
    end })
    local function install()
        LayoutA = {}
        LayoutA.events = { events.ready }
        function LayoutA.create() return 1 end
        LayoutB = {}
        LayoutB.events = { events.ready }
        function LayoutB.create() return 2 end
    end
    install()
    assert(trace == "readyready")
    assert(LayoutA.events[1] == "ready" and LayoutA.events[2] == nil)
    assert(LayoutB.events[1] == "ready" and LayoutB.events[2] == nil)
    assert(LayoutA.create() == 1 and LayoutB.create() == 2)
    print("global constructor field", trace, LayoutA.create(), LayoutB.create())
    events, LayoutA, LayoutB = saved_events, saved_a, saved_b
end

-- 未读的原常量 local 占据分支构造器的低槽前缀，不能在完整帧恢复前丢弃。
local function build_task_list(self, event)
    if event.action then
        local tasks = {}
        local unused = ""
        if event.action == "manual" then
            tasks = { Load.check, Load.login(event.from), Load.server, Load.reload }
        elseif event.action == "auto" then
            tasks = { Load.check, Load.server, Load.reload, Load.done }
        end
        return tasks
    end
end

local function check_task_list()
    local saved_load = Load
    local trace = ""
    local check, server, reload, done = {}, {}, {}, {}
    Load = setmetatable({}, { __index = function(_, key)
        trace = trace .. key .. ";"
        if key == "check" then return check end
        if key == "server" then return server end
        if key == "reload" then return reload end
        if key == "done" then return done end
        if key == "login" then
            return function(value)
                trace = trace .. "call;"
                return value, "extra"
            end
        end
    end })
    for scenario = 1, 3 do
        local value = nil
        if scenario == 2 then value = false end
        if scenario == 3 then value = "user" end
        trace = ""
        local tasks = build_task_list({}, { action = "manual", from = value })
        assert(tasks[1] == check and tasks[2] == value and tasks[3] == server)
        assert(tasks[4] == reload and tasks[5] == nil)
        assert(trace == "check;login;call;server;reload;")
        print("task list manual", scenario, tasks[2], trace)
    end
    trace = ""
    local tasks = build_task_list({}, { action = "auto" })
    assert(tasks[1] == check and tasks[2] == server and tasks[3] == reload and tasks[4] == done)
    assert(tasks[5] == nil and trace == "check;server;reload;done;")
    trace = ""
    assert(next(build_task_list({}, { action = "none" })) == nil)
    assert(build_task_list({}, {}) == nil and trace == "")
    print("task list alternate", tasks[4] == done)
    Load = saved_load
end
check_task_list()
