-- 原生 NOT 的分支内比较准备必须保持顺序、次数、操作数方向及短路出口。
-- unluac: expect-ast-count [[if]] [[0]] [[@proto=1]]
-- unluac: expect-ast-count [[if]] [[0]] [[@proto=2]]
-- unluac: expect-ast-count [[local-binding]] [[0]] [[@proto=1]]
-- unluac: expect-ast-count [[local-binding]] [[0]] [[@proto=2]]
-- unluac: expect-ast-count [[local-binding]] [[1]] [[@proto=3]]
-- unluac: expect-ast-count [[local-binding]] [[3]] [[@proto=6]]
local function conjunction(enabled, left, right)
    return enabled == true and not (left < right) and not (left > right)
        and not (left <= right) and not (left >= right)
end

local function disjunction(enabled, left, right)
    return enabled ~= true or not (left < right) or not (left > right)
        or not (left <= right) or not (left >= right)
end

local trace, stop, base, count
local function compare(kind, left, right)
    count = count + 1
    trace = trace .. kind .. left.name .. right.name .. ";"
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
    local ok, result = pcall(observer, enabled, left, right)
    local expected = enabled and (cut == 0 and 4 or math.abs(cut)) or 0
    assert(count == expected)
    assert(trace == (expected == 0 and "" or prefixes[expected]))
    if enabled and cut < 0 then
        assert(not ok and string.find(result, "comparison-stop", 1, true))
    else
        assert(ok)
        assert(result == ((enabled and cut == 0) ~= default))
    end
    print(default, enabled, cut, ok, count, trace)
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
