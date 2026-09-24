-- Luau inline capture preparation must retire with the original closure frame.
-- unluac: expect-not-contains [[= print]]
-- unluac: expect-not-contains [[= assert]]
-- unluac: expect-ast-count [[local-binding]] [[4]] [[@proto=0]]
local function make(value)
    return function(other) return value + other end
end
local first = make(3)
local second = make(9)
local duplicate = make(3)
assert(first ~= second and first ~= duplicate)
assert(duplicate(4) == 7)
assert(first(4) == 7)
assert(second(4) == 13)
print("value-capture-frame", first(5), second(5))
