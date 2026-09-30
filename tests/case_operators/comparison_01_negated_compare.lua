-- regress_248_luajit_negated_compare: ISGE/ISGT 是原关系的逻辑取反
-- unluac: expect-contains [[not]]
-- unluac: expect-not-contains [[unluac error]]
-- unluac: expect-ast-count [[function]] [[8]]
-- unluac: expect-ast-count [[if]] [[0]]
-- unluac: expect-ast-max [[local-binding]] [[13]]
-- unluac: expect-contains [[assert(r0_6(r0_3 % 4 >= 2, r0_3 % 2 == 1) == r0_5[r0_3 + 1])]] [[@dialect=luajit]]
-- 独立参数帧要把可能调用元方法的取模、调用和动态键保持在一条 assert 内。
-- unluac: expect-ast-count [[local-decl]] [[0]] [[@proto=7]] [[@dialect=luau]]
-- unluac: expect-contains [[assert(p7_2(p7_0 % 4 >= 2, p7_0 % 2 == 1) == p7_1[p7_0 + 1])]] [[@dialect=luau]]

local nan = 0 / 0
assert((nan >= 1) == false)
assert((not (nan < 1)) == true)
assert((nan > 1) == false)
assert((not (nan <= 1)) == true)

local calls = {}
local mt = {
    __lt = function(a, b)
        calls[#calls + 1] = "lt:" .. a.tag .. ":" .. b.tag
        return a.result
    end,
    __le = function(a, b)
        calls[#calls + 1] = "le:" .. a.tag .. ":" .. b.tag
        return a.result
    end,
}
local a = setmetatable({ tag = "a", result = false }, mt)
local b = setmetatable({ tag = "b", result = false }, mt)

assert((a >= b) == false)
assert(not (a < b))
assert((a > b) == false)
assert(not (a <= b))
assert(table.concat(calls, ",") == "le:b:a,lt:a:b,lt:b:a,le:a:b")

-- 比较参数的 RI 准备与 CALL 后动态索引必须按原顺序各求值一次。
mt.__mod = function(value, divisor)
    assert(value == a)
    calls[#calls + 1] = "mod:" .. divisor
    return 5 % divisor
end
mt.__add = function(value, increment)
    assert(value == a)
    calls[#calls + 1] = "add:" .. increment
    return 5 + increment
end
local expected = setmetatable({}, {__index = function(_, key)
    calls[#calls + 1] = "index:" .. key
    assert(key == 6)
    return "ok"
end})
local function consume(first, second)
    calls[#calls + 1] = "call"
    assert(first == false and second == true)
    return "ok"
end
calls = {}
assert(consume(a % 4 >= 2, a % 2 == 1) == expected[a + 1])
assert(table.concat(calls, ",") == "mod:4,mod:2,call,add:1,index:6")

local function parameter_frame(value, lookup, fn)
    assert(fn(value % 4 >= 2, value % 2 == 1) == lookup[value + 1])
end
calls = {}
parameter_frame(a, expected, consume)
assert(table.concat(calls, ",") == "mod:4,mod:2,call,add:1,index:6")

print("regress_248_luajit_negated_compare")

-- 参数比较不能被编译期常量折叠，四个返回位置分别观察原关系与逻辑补集。
local function nan_comparisons(value)
    return value >= 1, not (value < 1), value > 1, not (value <= 1)
end
local ge, not_lt, gt, not_le = nan_comparisons(nan)
assert(ge == false and not_lt == true and gt == false and not_le == true)
ge, not_lt, gt, not_le = nan_comparisons(1)
assert(ge == true and not_lt == true and gt == false and not_le == false)
ge, not_lt, gt, not_le = nan_comparisons(2)
assert(ge == true and not_lt == true and gt == true and not_le == true)
ge, not_lt, gt, not_le = nan_comparisons(-math.huge)
assert(ge == false and not_lt == false and gt == false and not_le == false)
assert(select("#", nan_comparisons(nan)) == 4)

calls = {}
a.result, b.result = true, false
assert((a >= b) == false)
assert((not (a < b)) == false)
assert((a > b) == false)
assert((not (a <= b)) == false)
assert(table.concat(calls, ",") == "le:b:a,lt:a:b,lt:b:a,le:a:b")
calls = {}
a.result, b.result = nil, 0
assert((a >= b) == true)
assert((not (a < b)) == true)
assert((a > b) == true)
assert((not (a <= b)) == true)
assert(table.concat(calls, ",") == "le:b:a,lt:a:b,lt:b:a,le:a:b")
calls = {}
assert(select("#", parameter_frame(a, expected, consume)) == 0)
assert(table.concat(calls, ",") == "mod:4,mod:2,call,add:1,index:6")
