-- unluac: expect-contains [[local r1_0, r1_1 = 160, 1]]
-- unluac: expect-contains [[if p1_0 == "mobile" and p1_1 ~= "tablet" then]]
-- unluac: expect-contains [[r1_0, r1_1 = 120, 0.5]]
-- unluac: expect-contains [[return r1_0, r1_1]]
-- unluac: expect-not-contains [[local r1_2]]
-- unluac: expect-not-contains [[if r1_2 == "tablet"]]
-- unluac: expect-not-contains [[unluac error]]

local function choose_layout(kind, form)
    local offset, scale = 160, 1
    if kind == "mobile" and form ~= "tablet" then
        scale = 0.5
        offset = 120
    end
    return offset, scale
end

print("regress_68_multi_value_merge_defer_to_bvm#1", choose_layout("mobile", "phone"))
