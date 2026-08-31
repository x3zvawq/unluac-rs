-- unluac: expect-not-contains [[nil == false]]
-- unluac: expect-not-contains [[true == "true"]]
-- unluac: expect-not-contains [[7 == "7"]]
-- unluac: expect-contains [[return false, false, false]]

local function compare_mismatched_primitives()
    return nil == false, true == "true", 7 == "7"
end

local nil_boolean, boolean_string, number_string = compare_mismatched_primitives()
assert(not nil_boolean and not boolean_string and not number_string)

return nil_boolean, boolean_string, number_string
