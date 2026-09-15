-- regress_248_luajit_negated_compare: ISGE/ISGT 是原关系的逻辑取反
-- unluac: expect-contains [[not]]
-- unluac: expect-not-contains [[unluac error]]
-- unluac: expect-contains [[assert(r0_6(2 <= r0_3 % 4, r0_3 % 2 == 1) == r0_5[r0_3 + 1])]] [[@dialect=luajit]]
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
        return false
    end,
    __le = function(a, b)
        calls[#calls + 1] = "le:" .. a.tag .. ":" .. b.tag
        return false
    end,
}
local a = setmetatable({ tag = "a" }, mt)
local b = setmetatable({ tag = "b" }, mt)

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
