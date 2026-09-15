-- regress_319_luau_captured_shared_diamond: shared closure DAG 的 diamond occurrence 必须保留 alias 证明
-- unluac: expect-not-contains [[unresolved]]
-- unluac: expect-not-contains [[unluac error]]
local function opaque(value)
    return value
end

local stable = opaque(7)

local function diamond_factory()
    local function leaf()
        return stable
    end
    local function left()
        return leaf()
    end
    local function right()
        return leaf()
    end
    return function()
        return left(), right()
    end
end

local first = diamond_factory()
local second = diamond_factory()
local first_left, first_right = first()
local second_left, second_right = second()
assert(first == second)
assert(first_left == 7 and first_right == 7 and second_left == 7 and second_right == 7)
print(
    "regress_319_positive",
    first == second,
    first_left == second_left,
    first_right == second_right
)

local function alias_guard(flag)
    local function leaf_a()
        return stable + 1
    end
    local function leaf_b()
        return stable + 2
    end
    local function left()
        return (flag and leaf_a or leaf_b)()
    end
    local function right()
        return (flag and leaf_a or leaf_b)()
    end
    return function()
        return left(), right()
    end
end

local alias_first = alias_guard(true)
local alias_second = alias_guard(false)
local alias_first_left, alias_first_right = alias_first()
local alias_second_left, alias_second_right = alias_second()
assert(alias_first ~= alias_second)
assert(alias_first_left == 8 and alias_first_right == 8)
assert(alias_second_left == 9 and alias_second_right == 9)
print(
    "regress_319_alias_guard",
    alias_first == alias_second,
    alias_first_left == alias_first_right,
    alias_second_left == alias_second_right
)
