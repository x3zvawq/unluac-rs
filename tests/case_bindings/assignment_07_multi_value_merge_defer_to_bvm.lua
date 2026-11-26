-- unluac: expect-not-contains [[local r1_2]]
-- unluac: expect-not-contains [[if r1_2 == "tablet"]]

local function choose_layout(kind, form)
    local offset, scale = 160, 1
    if kind == "mobile" and form ~= "tablet" then
        scale = 0.5
        offset = 120
    end
    return offset, scale
end

local offset, scale = choose_layout("mobile", "phone")
assert(offset == 120 and scale == 0.5)
print("regress_68_multi_value_merge_defer_to_bvm#1", offset, scale)
