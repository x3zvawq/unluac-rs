-- regress_299_luau_captured_shared_owner_dependency: 同一closure不能既作factory owner又被复合DAG消费
-- unluac: expect-not-contains [[unresolved]]
-- unluac: expect-not-contains [[unluac error]]
local function opaque(value)
    return value
end

local value = opaque(0 / 0)
local function outer_factory()
    local function inner_factory()
        return function()
            return value
        end
    end
    probe = inner_factory()
    return function()
        return inner_factory
    end
end

local first = outer_factory()
local first_probe = probe
local second = outer_factory()
print(
    "regress_299_result",
    first ~= second,
    first() ~= second(),
    first_probe ~= probe,
    probe() ~= probe()
)
