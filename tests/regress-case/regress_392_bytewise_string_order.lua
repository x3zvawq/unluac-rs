-- unluac: expect-not-contains [["ä" < "z"]]
-- unluac: expect-not-contains [["ä" <= "z"]]
-- unluac: expect-contains [[return false, false]]

local function compare_strings()
    return "ä" < "z", "ä" <= "z"
end

local less, less_equal = compare_strings()
assert(not less and not less_equal)

return less, less_equal
