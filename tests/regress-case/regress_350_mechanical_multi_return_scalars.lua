-- regress_350_mechanical_multi_return_scalars: mechanical run may inline proven scalar expressions into top-level return slots
-- unluac: expect-contains [[return p1_0 + 1, p1_1 + 2]]
-- unluac: expect-contains [[return p3_0 == 42]]
-- unluac: expect-not-contains [[local r1_0 = p1_0 + 1]]
-- unluac: expect-not-contains [[local r1_1 = p1_1 + 2]]
local function run(lhs, rhs)
    local first = lhs + 1
    local second = rhs + 2
    if false then
        print(first, second)
    end
    return first, second
end

local first, second = run(40, 40)
assert(first == 41 and second == 42)

local function identity(value)
    return value
end

local function compare(value)
    local compared = value == 42
    return compared, identity(value)
end

local matches, echoed = compare(42)
assert(matches and echoed == 42)
