-- unluac: expect-contains [[r1_1 = r1_0]]
-- unluac: expect-contains [[r1_1 = r0_0.CENTER_JUSTIFY]]
-- unluac: expect-not-contains [[r1_1 = p1_0]]
-- unluac: expect-not-contains [[unluac error]]

local text_box = {
    CENTER_JUSTIFY = "center",
    LEFT_JUSTIFY = "left",
    RIGHT_JUSTIFY = "right",
}

local function choose_alignment(h_align)
    local h_just = text_box.CENTER_JUSTIFY
    if h_align and h_align == "left" then
        h_just = text_box.LEFT_JUSTIFY
    end

    local h_alignment
    if h_align then
        if h_align == "right" then
            h_alignment = text_box.RIGHT_JUSTIFY
        else
            h_alignment = h_just
        end
    else
        h_alignment = text_box.CENTER_JUSTIFY
    end
    return h_alignment
end

local center = choose_alignment(nil)
local left = choose_alignment("left")
local right = choose_alignment("right")
assert(center == "center" and left == "left" and right == "right")
print("regress_66_preserved_value_guard#1", center, left, right)
