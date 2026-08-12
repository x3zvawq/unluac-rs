-- regress_296_luau_captured_shared_factory: O2内联后的带capture DUPCLOSURE必须恢复共同词法owner
-- unluac: expect-not-contains [[unresolved]]
-- unluac: expect-not-contains [[unluac error]]
-- unluac: expect-not-contains [[rawequal]]
local function opaque(value)
    return value
end

local nan = opaque(0 / 0)
local function transitive_factory()
    local function owner(...)
        return nan
    end
    return function()
        return owner()
    end
end

local transitive_first = transitive_factory()
local transitive_second = transitive_factory()
print(
    "regress_296_transitive",
    transitive_first == transitive_second,
    transitive_first() ~= transitive_first(),
    transitive_second() ~= transitive_second()
)

local stable = opaque(7)
local function noisy_factory(tag)
    print("regress_296_event", tag)
    local function owner(...)
        return stable
    end
    return function()
        return owner()
    end
end

local noisy_first = noisy_factory("first")
local noisy_second = noisy_factory("second")
print("regress_296_noisy", noisy_first == noisy_second, noisy_first(), noisy_second())

local function noisy_nan_factory(tag)
    print("regress_296_nan_event", tag)
    local function owner(...)
        return nan
    end
    return function()
        return owner()
    end
end

local noisy_nan_first = noisy_nan_factory("first")
local noisy_nan_second = noisy_nan_factory("second")
print(
    "regress_296_noisy_nan",
    noisy_nan_first == noisy_nan_second,
    noisy_nan_first() ~= noisy_nan_first(),
    noisy_nan_second() ~= noisy_nan_second()
)

local function branch_factory()
    return function()
        return stable
    end
end

local branch_first
if opaque(true) then
    branch_first = branch_factory()
else
    branch_first = branch_factory()
end
local branch_second = branch_factory()
print("regress_296_branch", branch_first == branch_second, branch_first(), branch_second())
