-- 循环状态共享一个 cell，每轮 captured 则独立关闭；退出值是返回时的快照。
-- unluac: expect-not-contains [[while true do]]
-- unluac: expect-contains [[while i < limit do]] [[@debug=retained]]
-- unluac: expect-contains [[return funcs, i]] [[@debug=retained]]
-- unluac: expect-ast-count [[local-binding]] [[18]]
-- unluac: expect-ast-count [[while]] [[1]]
-- unluac: expect-ast-count [[break]] [[1]]
local function collect(limit)
    local funcs = {}
    local i = 0
    while i < limit do
        i = i + 1
        local captured = i * 5
        funcs[#funcs + 1] = function(extra, bump)
            i = i + (bump or 0)
            return captured + extra, i
        end
        if i == 3 then
            break
        end
    end
    return funcs, i
end

local empty, zero = collect(0)
assert(#empty == 0 and zero == 0)
local normal, normal_i = collect(2)
local broken, broken_i = collect(6)
assert(#normal == 2 and normal_i == 2 and #broken == 3 and broken_i == 3)
local a, b = broken[1](2, 10)
local c, d = broken[3](4)
assert(a == 7 and b == 13 and c == 19 and d == 13 and broken_i == 3)
local e, f = normal[1](0, 1)
local g, h = normal[2](0)
assert(e == 5 and f == 3 and g == 10 and h == 3 and normal_i == 2)
print("captured-state-exit", zero, normal_i, broken_i, a, b, c, d, e, f, g, h)
