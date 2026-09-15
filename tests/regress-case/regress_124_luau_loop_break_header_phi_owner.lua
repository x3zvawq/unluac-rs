-- regress_124_luau_loop_break_header_phi_owner#1: nested break branch 的入口 phi 继承 active loop state owner
-- unluac: expect-contains [[repeat]]
-- unluac: expect-contains [[break]]
-- unluac: expect-not-contains [[not p1_0 or not p1_1]]
-- unluac: expect-not-contains [[goto ]]
-- unluac: expect-not-contains [[::L]]
-- unluac: expect-not-contains [[unresolved]]
-- unluac: expect-not-contains [[unluac error]]
local subject = function(a, b, t)
    local x = 0
    for _ in t do
        repeat
            if a then
                while b do
                    x += 1
                end
            else
                if not a or not b then
                    x += 1
                    if b then
                        break
                    end
                end
            end
            x += 0
        until a
    end
    return x
end

local dispatch = { subject }
for _, values in ipairs({ {}, { 10 }, { 10, 20, 30, 40 } }) do
    local broken = dispatch[1](false, true, values)
    local normal = dispatch[1](true, false, values)
    assert(broken == #values and normal == 0)
    print("regress_124#1", #values, broken, normal)
end
-- 两种非终止参数组合仅在空迭代域调用；有限运行不声称覆盖这些无限循环体。
assert(dispatch[1](false, false, {}) == 0)
assert(dispatch[1](true, true, {}) == 0)
