-- 固定结果先写回旧绑定，随后较窄 CALL 和新声明复用同一 scratch 区。
-- unluac: expect-ast-count [[empty-local]] [[0]]
-- unluac: expect-ast-count [[local-binding]] [[12]] [[@proto=0]]
-- unluac: expect-contains [[first, second, count, value = results(3)]] [[@debug=retained]]
-- unluac: expect-contains [[first, second, value = shorter()]] [[@debug=retained]]
local trace = ""
local function results(count)
    trace = trace .. count
    return "first", "second", count, 11
end
local function shorter()
    trace = trace .. "s"
    return "short", nil, 17
end
local function final()
    trace = trace .. "f"
    return "outer", "inner", nil, 23
end
local first, second, count, value = results(2)
assert(first == "first" and second == "second" and count == 2 and value == 11)
first, second, count, value = results(3)
assert(first == "first" and second == "second" and count == 3 and value == 11)
first, second, value = shorter()
assert(first == "short" and second == nil and count == 3 and value == 17)
local outer, inner, absent, last = final()
assert(outer == "outer" and inner == "inner" and absent == nil and last == 23)
assert(trace == "23sf")
print("results_09_reused_writeback_versions", trace, count, value, last)
