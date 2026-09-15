-- regress_432_open_constructor_multiple_setlists: a fixed SETLIST batch may precede the final open batch
-- unluac: expect-contains [[local r0_1 = {]]
-- unluac: expect-not-contains [[local r0_1 = {}]]
-- unluac: expect-not-contains [[table-set-list]]
-- unluac: expect-not-contains [[unluac error]]
local function tail()
    return 51, 52, 53
end

local values = {
    1, 2, 3, 4, 5, 6, 7, 8, 9, 10,
    11, 12, 13, 14, 15, 16, 17, 18, 19, 20,
    21, 22, 23, 24, 25, 26, 27, 28, 29, 30,
    31, 32, 33, 34, 35, 36, 37, 38, 39, 40,
    41, 42, 43, 44, 45, 46, 47, 48, 49, 50,
    tail(),
}

assert(#values == 53)
assert(values[1] == 1 and values[50] == 50)
assert(values[51] == 51 and values[52] == 52 and values[53] == 53)
print("regress_432_open_constructor_multiple_setlists", "ok")
