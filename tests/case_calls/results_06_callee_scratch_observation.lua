-- unluac: expect-ast-min [[local-decl]] [[1]] [[@proto=15]]
-- unluac: expect-ast-min [[local-decl]] [[1]] [[@proto=16]]
-- 终结调用也可能观察原 callee COPY 覆盖的未知 scratch，不能统一改成 make()()。
-- unluac: expect-ast-min [[local-decl]] [[1]] [[@proto=5]]
-- unluac: expect-ast-max [[local-decl]] [[0]] [[@proto=6]]
-- unluac: expect-ast-min [[local-decl]] [[1]] [[@proto=9]]
-- unluac: expect-ast-max [[local-decl]] [[0]] [[@proto=10]]
-- unluac: expect-ast-min [[local-decl]] [[1]] [[@proto=8]]
-- 无观察不代表没有后续可见的槽写；下方 post-return 场景要求保留该 COPY。
-- unluac: expect-ast-min [[local-decl]] [[1]] [[@proto=13]] [[@dialect=lua5.4]] [[@debug=stripped]]
-- 单结果返回帧收回 callee 准备，具名 debug 结果仍保留。
-- unluac: expect-ast-count [[local-binding]] [[0]] [[@proto=27]] [[@debug=stripped]]
-- unluac: expect-ast-count [[local-binding]] [[1]] [[@proto=27]] [[@debug=retained]]
local check, report = assert, print
local make_counter = setmetatable
local weak = setmetatable({}, { __mode = "v" })
local results = {}
local function observe()
    collectgarbage("collect")
    results[#results + 1] = weak[1] ~= nil
    return function() end
end
local _ENV = setmetatable({}, { __index = observe })
local function make()
    local resource = {}
    weak[1] = resource
    return function() missing() end
end
local function copied()
    local f = make()
    f()
end
local function nested()
    make()()
end
copied()
nested()
check(results[1] == false and results[2] == true)

-- 即使 maker 从 r0 返回闭包，callee 帧下移仍会改变后续 LOAD 对旧 scratch 的覆盖。
local function make_low_return()
    local f = function()
        local n = 1
        missing()
        return n
    end
    local resource = {}
    weak[1] = resource
    return f
end
local function copied_low_return()
    local f = make_low_return()
    f()
end
local function nested_low_return()
    make_low_return()()
end
copied_low_return()
nested_low_return()
check(results[3] == false and results[4] == true)

-- 正文仅写已捕获的布尔值；LOADTRUE 仍写物理槽，返回后也可能被后继调用观察。
local reached = false
local function make_eventless()
    return function() reached = true end
end
local function call_eventless()
    local f = make_eventless()
    f()
end
call_eventless()
check(reached)
report("regress_648", results[1], results[2])

-- 没有后续 CALL 也须保留原槽覆盖：返回值的全局 lookup 自身就能观察入口残值。
local function seed_entry(dummy, resource)
    weak[1] = resource
    return true
end
local function entry_not(value)
    local unused = not value
    return missing
end
local function entry_equal(value)
    local unused = value == nil
    return missing
end
local function entry_erased(value)
    return missing
end
local function drive_entry(fn)
    do local dummy = seed_entry(false, {}) end
    fn(false)
end
drive_entry(entry_not)
drive_entry(entry_equal)
drive_entry(entry_erased)
check(results[5] == false and results[6] == false and results[7] == true)

-- 表面只有 upvalue 加法也可能通过 __add 观察：不能把“无显式 CALL”当作无事件。
-- unluac: expect-ast-min [[local-decl]] [[1]] [[@proto=22]]
-- unluac: expect-ast-max [[local-decl]] [[0]] [[@proto=23]]
local counter = make_counter({}, {__add = function(value)
    observe()
    return value
end})
local function make_arithmetic()
    local f = function() counter = counter + 1 end
    local resource = {}
    weak[1] = resource
    return f
end
local function copied_arithmetic()
    local f = make_arithmetic()
    f()
end
local function nested_arithmetic()
    make_arithmetic()()
end
copied_arithmetic()
nested_arithmetic()
check(results[8] == false and results[9] == true)
report("terminal-arithmetic", results[8], results[9])

-- 返回后的 lookup 也会看到 callee 的原槽覆盖，不能只检查 callee 执行中的观察。
local function nested_eventless() make_eventless()() end
local function fresh_post_root()
    local object = {}
    weak[1] = object
    return object
end
local function post_observer()
    local result = missing
    local a, b, c, d = false, false, false, false
    return result, "discarded"
end
local function drive_post(fn)
    -- 后续实参覆盖 fresh 的返回残副本，弱表只观察第三个实参的原槽。
    fn(nil, nil, fresh_post_root(), false, false, false, false)
    local result = post_observer()
    return result
end
drive_post(call_eventless)
drive_post(nested_eventless)
check(results[10] == false and results[11] == true)
report("terminal-post-return", results[10], results[11])

-- 真正不写任何槽的零参数闭包仍可合并，防止修复退化为全面禁用。
-- unluac: expect-ast-count [[local-decl]] [[0]] [[@proto=30]] [[@dialect=lua5.3]] [[@debug=stripped]]
-- unluac: expect-ast-count [[local-decl]] [[0]] [[@proto=30]] [[@dialect=lua5.4]] [[@debug=stripped]]
-- unluac: expect-ast-count [[local-decl]] [[0]] [[@proto=30]] [[@dialect=lua5.5]] [[@debug=stripped]]
local function make_no_write() return function() end end
local function call_no_write()
    local f = make_no_write()
    f()
end
drive_post(call_no_write)
check(results[12] == true)

-- 空正文也可能在入口补 nil；缺失形参的隐式写槽不能借用无写闭包的许可。
-- unluac: expect-ast-min [[local-decl]] [[1]] [[@proto=33]] [[@dialect=lua5.4]] [[@debug=stripped]]
local function make_missing_parameter() return function(unused) end end
local function call_missing_parameter()
    local f = make_missing_parameter()
    f()
end
-- 普通 CALL 的固定单结果不能恢复为尾调用或开放返回，把第二个返回值带出来。
local first_result, extra_result = drive_post(call_missing_parameter)
check(first_result ~= nil and extra_result == nil)
check(results[13] == false)
report("terminal-missing-parameter", results[13])
