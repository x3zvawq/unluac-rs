-- regress_414_constructor_field_name_sugar: constructor string keys share field-access legality
-- unluac: expect-contains [[alpha = 1]]
-- unluac: expect-not-contains [["alpha"] = 1]]
-- unluac: expect-contains [[["end"] = 2]]
-- unluac: expect-contains [[["bad-key"] = 3]]
-- unluac: expect-contains [[["\255"] = 4]]

local alpha_key, keyword_key, invalid_key, byte_key = "alpha", "end", "bad-key", "\255"
local values = {
    [alpha_key] = 1,
    [keyword_key] = 2,
    [invalid_key] = 3,
    [byte_key] = 4,
}

assert(values.alpha == 1)
assert(values["end"] == 2)
assert(values["bad-key"] == 3)
assert(values[string.char(255)] == 4)
print("regress_414_constructor_field_name_sugar", "OK")
