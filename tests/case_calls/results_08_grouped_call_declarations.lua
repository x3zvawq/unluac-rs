-- CALL 在并列 local 的共同 scratch 求值，单值结果按原顺序写回各声明槽。
-- unluac: expect-ast-max [[empty-local]] [[0]]
-- unluac: expect-contains [[local first, second, third = result("a"), result("b"), result("c")]] [[@debug=retained]]
-- unluac: expect-contains [[local r0_2, r0_3, r0_4 = r0_1("a"), r0_1("b"), r0_1("c")]] [[@debug=stripped]] [[@dialect=luau]]
-- unluac: expect-count [[= setmetatable({}, {}), setmetatable({}, {})]] [[1]] [[@dialect=luau]]
-- 反向比较树仍在原 Boolean 参数帧求值，不另造 nil 和条件 carrier。
-- unluac: expect-not-contains [[ = nil]]
-- unluac: expect-contains [[assert(left ~= right and getmetatable(left) ~= getmetatable(right)]] [[@debug=retained]]
-- unluac: expect-not-contains [[assert(not (]]
-- unluac: expect-contains [[return lhs ~= rhs and observed(lhs) ~= observed(rhs)]] [[@debug=retained]]
-- unluac: expect-ast-count [[local-binding]] [[0]] [[@proto=1]]
-- unluac: expect-ast-count [[local-binding]] [[0]] [[@proto=2]]
-- unluac: expect-ast-count [[local-binding]] [[0]] [[@proto=3]]
-- unluac: expect-ast-count [[local-binding]] [[0]] [[@proto=4]]
local trace = ""
local function result(value)
    trace = trace .. value
    return value, "extra"
end
local first, second, third = result("a"), result("b"), result("c")
local left, right = setmetatable({}, {}), setmetatable({}, {})
assert(trace == "abc")
assert(first == "a" and second == "b" and third == "c")
assert(left ~= right and getmetatable(left) ~= getmetatable(right))
left.key = 7
assert(right.key == nil)
print("results_08_grouped_call_declarations", trace, first, second, third, left.key)

-- 比较方向整理不能交换 __eq 与后续调用，也不能在首项为 false 时求右侧。
local equality_trace = ""
local equality_mt = {
    __eq = function(lhs, rhs)
        equality_trace = equality_trace .. lhs.label .. rhs.label
        return lhs.value == rhs.value
    end,
}
local function observed(value)
    equality_trace = equality_trace .. "[" .. value.label .. "]"
    return value
end
local function distinct(lhs, rhs)
    return lhs ~= rhs and observed(lhs) ~= observed(rhs)
end
local a = setmetatable({ label = "a", value = 1 }, equality_mt)
local b = setmetatable({ label = "b", value = 2 }, equality_mt)
local c = setmetatable({ label = "c", value = 1 }, equality_mt)
assert(distinct(a, b))
assert(equality_trace == "ab[a][b]ab", equality_trace)
equality_trace = ""
assert(not distinct(a, c))
assert(equality_trace == "ac", equality_trace)
