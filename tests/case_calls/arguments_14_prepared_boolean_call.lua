-- 普通调用须先读取 callee，再按短路路径准备带原生 NOT 的 Boolean 参数。
-- unluac: expect-ast-count [[if]] [[0]] [[@proto=3]]
-- unluac: expect-ast-count [[if]] [[0]] [[@proto=4]]
-- unluac: expect-ast-count [[local-binding]] [[0]] [[@proto=3]]
-- unluac: expect-ast-count [[local-binding]] [[0]] [[@proto=4]]
-- unluac: expect-ast-count [[call]] [[1]] [[@proto=3]]
-- unluac: expect-ast-count [[call]] [[1]] [[@proto=4]]
local observed, deliveries
local function receive(value)
    observed = value
    deliveries = deliveries + 1
end
local function poisoned()
    error("callee-read-too-late")
end
local active = receive
local function conjunction(enabled, left, right)
    active(enabled == true and not (left < right) and not (left > right)
        and not (left <= right) and not (left >= right))
end
local function disjunction(enabled, left, right)
    active(enabled ~= true or not (left < right) or not (left > right)
        or not (left <= right) or not (left >= right))
end

local trace, stop, base, count
local function compare(kind, left, right)
    count = count + 1
    trace = trace .. kind .. left.name .. right.name .. ";"
    active = poisoned
    if stop == -count then error("comparison-stop") end
    if count == stop then return not base end
    return base
end
local meta = {
    __lt = function(left, right) return compare("lt", left, right) end,
    __le = function(left, right) return compare("le", left, right) end,
}
local left = setmetatable({ name = "L" }, meta)
local right = setmetatable({ name = "R" }, meta)
local prefixes = { "ltLR;", "ltLR;ltRL;", "ltLR;ltRL;leLR;", "ltLR;ltRL;leLR;leRL;" }
local function run(observer, default, enabled, cut)
    trace, count, base, stop = "", 0, default, cut
    observed, deliveries, active = nil, 0, receive
    local ok, result = pcall(observer, enabled, left, right)
    local expected = enabled and (cut == 0 and 4 or math.abs(cut)) or 0
    assert(count == expected)
    assert(trace == (expected == 0 and "" or prefixes[expected]))
    if enabled and cut < 0 then
        assert(not ok and string.find(result, "comparison-stop", 1, true))
        assert(deliveries == 0 and observed == nil)
    else
        assert(ok and result == nil and deliveries == 1)
        assert(observed == ((enabled and cut == 0) ~= default))
    end
    print(default, enabled, cut, ok, count, trace, deliveries, observed)
end
run(conjunction, false, false, 0)
run(disjunction, true, false, 0)
run(conjunction, false, true, 0)
run(disjunction, true, true, 0)
for cut = 1, 4 do
    run(conjunction, false, true, cut)
    run(disjunction, true, true, cut)
    run(conjunction, false, true, -cut)
    run(disjunction, true, true, -cut)
end
