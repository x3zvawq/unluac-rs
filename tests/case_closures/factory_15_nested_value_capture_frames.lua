-- Nested factories preserve distinct lexical captures and fresh closure identity.
-- unluac: expect-not-contains [[= print]]
-- unluac: expect-not-contains [[= assert]]
-- unluac: expect-ast-count [[local-binding]] [[4]] [[@proto=0]]
local function outer(value)
    local function make(argument)
        return function(other) return argument + other + value end
    end
    return make(value)
end
local first = outer(3)
local second = outer(9)
local duplicate = outer(3)
assert(first ~= second and first ~= duplicate)
assert(duplicate(4) == 10)
assert(first(4) == 10)
assert(second(4) == 22)
print("nested-value-capture-frame", first(5), second(5))
