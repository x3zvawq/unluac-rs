-- 单结果 CALL 后紧邻常量写覆盖原结果槽；其结果与旧 callee 都不能延长到下次观察。
-- 原作用域末端也决定下一次 CALL 的槽位，不能把未读结果接到更晚的同槽对象。
-- unluac: expect-ast-count [[do-block]] [[1]] [[@proto=8]] [[@dialect=lua5.1]]
-- unluac: expect-ast-count [[local-decl]] [[2]] [[@proto=8]] [[@dialect=lua5.1]]
-- unluac: expect-ast-count [[do-block]] [[0]] [[@proto=9]] [[@dialect=lua5.1]]
-- unluac: expect-ast-count [[do-block]] [[1]] [[@proto=8]] [[@dialect=lua5.2]]
-- unluac: expect-ast-count [[local-decl]] [[2]] [[@proto=8]] [[@dialect=lua5.2]]
-- unluac: expect-ast-count [[do-block]] [[0]] [[@proto=9]] [[@dialect=lua5.2]]
-- unluac: expect-ast-count [[do-block]] [[1]] [[@proto=8]] [[@dialect=lua5.3]]
-- unluac: expect-ast-count [[local-decl]] [[2]] [[@proto=8]] [[@dialect=lua5.3]]
-- unluac: expect-ast-count [[do-block]] [[0]] [[@proto=9]] [[@dialect=lua5.3]]
-- unluac: expect-ast-count [[do-block]] [[1]] [[@proto=8]] [[@dialect=lua5.4]]
-- unluac: expect-ast-count [[local-decl]] [[2]] [[@proto=8]] [[@dialect=lua5.4]]
-- unluac: expect-ast-count [[do-block]] [[0]] [[@proto=9]] [[@dialect=lua5.4]]
-- unluac: expect-ast-count [[do-block]] [[1]] [[@proto=8]] [[@dialect=lua5.5]]
-- unluac: expect-ast-count [[local-decl]] [[2]] [[@proto=8]] [[@dialect=lua5.5]]
-- unluac: expect-ast-count [[do-block]] [[0]] [[@proto=9]] [[@dialect=lua5.5]]
-- unluac: expect-ast-count [[do-block]] [[1]] [[@proto=2]] [[@dialect=luajit]]
-- unluac: expect-ast-count [[local-decl]] [[2]] [[@proto=2]] [[@dialect=luajit]]
-- unluac: expect-ast-count [[do-block]] [[0]] [[@proto=1]] [[@dialect=luajit]]
-- unluac: expect-contains [[local value = factory() and false or 9]] [[@debug=retained]]
-- unluac: expect-ast-count [[local-binding]] [[1]] [[@proto=3]] [[@dialect=lua5.1]]
-- unluac: expect-ast-count [[if]] [[0]] [[@proto=3]] [[@dialect=lua5.1]]
-- unluac: expect-ast-count [[local-binding]] [[1]] [[@proto=9]] [[@dialect=lua5.1]]
-- unluac: expect-ast-count [[assign]] [[1]] [[@proto=9]] [[@dialect=lua5.1]]
-- unluac: expect-ast-count [[local-binding]] [[1]] [[@proto=3]] [[@dialect=lua5.2]]
-- unluac: expect-ast-count [[if]] [[0]] [[@proto=3]] [[@dialect=lua5.2]]
-- unluac: expect-ast-count [[local-binding]] [[1]] [[@proto=9]] [[@dialect=lua5.2]]
-- unluac: expect-ast-count [[assign]] [[1]] [[@proto=9]] [[@dialect=lua5.2]]
-- unluac: expect-ast-count [[local-binding]] [[1]] [[@proto=3]] [[@dialect=lua5.3]]
-- unluac: expect-ast-count [[if]] [[0]] [[@proto=3]] [[@dialect=lua5.3]]
-- unluac: expect-ast-count [[local-binding]] [[1]] [[@proto=9]] [[@dialect=lua5.3]]
-- unluac: expect-ast-count [[assign]] [[1]] [[@proto=9]] [[@dialect=lua5.3]]
-- unluac: expect-ast-count [[local-binding]] [[1]] [[@proto=3]] [[@dialect=lua5.4]]
-- unluac: expect-ast-count [[if]] [[0]] [[@proto=3]] [[@dialect=lua5.4]]
-- unluac: expect-ast-count [[local-binding]] [[1]] [[@proto=9]] [[@dialect=lua5.4]]
-- unluac: expect-ast-count [[assign]] [[1]] [[@proto=9]] [[@dialect=lua5.4]]
-- unluac: expect-ast-count [[local-binding]] [[1]] [[@proto=3]] [[@dialect=lua5.5]]
-- unluac: expect-ast-count [[if]] [[0]] [[@proto=3]] [[@dialect=lua5.5]]
-- unluac: expect-ast-count [[local-binding]] [[1]] [[@proto=9]] [[@dialect=lua5.5]]
-- unluac: expect-ast-count [[assign]] [[1]] [[@proto=9]] [[@dialect=lua5.5]]
-- unluac: expect-ast-count [[local-binding]] [[1]] [[@proto=7]] [[@dialect=luajit]]
-- unluac: expect-ast-count [[if]] [[0]] [[@proto=7]] [[@dialect=luajit]]
-- unluac: expect-ast-count [[local-binding]] [[1]] [[@proto=1]] [[@dialect=luajit]]
-- unluac: expect-ast-count [[assign]] [[1]] [[@proto=1]] [[@dialect=luajit]]
-- unluac: expect-ast-count [[empty-local]] [[0]]
local weak = setmetatable({}, {__mode = "v"})
local trace = ""
local function result()
    trace = trace .. "call;"
    local object = {}
    weak.result = object
    return object, "discarded"
end
local function observe(value)
    collectgarbage("collect")
    collectgarbage("collect")
    assert(weak.result == nil)
    assert(value == 9)
    trace = trace .. "observe;"
end
local function run(factory, inspect)
    local value = (factory() and false) or 9
    inspect(value)
end
run(result, observe)
assert(trace == "call;observe;")
print("discarded-result", trace)

-- 六个固定参数补齐缺省 nil；不依赖被调函数的局部简化，单独观察 caller 的 CALL base。
local function fill_parameters(a, b, c, d, e, f)
    return a
end
local scratch_weak = setmetatable({}, {__mode = "v"})
local observations = {}
local function seed(a, b, c, d, e, f, resource)
    scratch_weak.value = resource
    return true
end
local methods = setmetatable({}, {__index = function()
    collectgarbage("collect")
    collectgarbage("collect")
    observations[#observations + 1] = type(scratch_weak.value)
    return function() end
end})
local function scoped_result(callback)
    do local result = seed(false, false, false, false, false, false, {}) end
    callback(true)
    methods.observe()
    local reserve = {1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12}
    return reserve[1]
end
-- 对照：声明确实跨过 CALL 时必须保留，不能把所有未读结果都缩域。
local function extended_result(callback)
    local result = seed(false, false, false, false, false, false, {})
    callback(true)
    methods.observe()
    result = {1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12}
    return result[1]
end
collectgarbage("stop")
scoped_result(fill_parameters)
extended_result(fill_parameters)
collectgarbage("restart")
assert(observations[1] == "table")
assert(observations[2] == "nil")

-- 原空 TEST 要保留，但不能因此把随后覆盖的调用结果延长到 observer。
do
    local value = result()
    if value then end
    value = 9
    observe(value)
end
