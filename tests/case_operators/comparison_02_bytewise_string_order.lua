-- unluac: expect-contains [[return "ä" < "z", "ä" <= "z"]]

local function compare_strings()
    return "ä" < "z", "ä" <= "z"
end

local less, less_equal = compare_strings()
assert(not less and not less_equal)

return less, less_equal
