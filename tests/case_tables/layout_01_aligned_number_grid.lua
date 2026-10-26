-- aligned style pins the number-grid layout for homogeneous numeric arrays.
-- The 40-element table exceeds one line, so the aligned style emits space-aligned
-- columns; recompile rounds keep the emitted grid valid Lua 5.1.
-- unluac: expect-contains [[    2,   3,   5,   7,   11,  13,  17,  19,  23,  29,  31,  37,  41,  43,]]
-- unluac: expect-contains [[109, 113, 127, 131, 137, 139, 149, 151, 157, 163, 167, 173,]]
-- unluac: expect-max-line-length [[100]]
local primes = {
    2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71,
    73, 79, 83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137, 139, 149, 151, 157, 163, 167, 173,
}
local function sum(list)
    local total = 0
    for index = 1, #list do
        total = total + list[index]
    end
    return total
end
print(sum(primes))
