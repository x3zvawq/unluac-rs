-- regress_298_luau_captured_shared_capture_free_dependency: 复合factory独占零capture依赖
-- unluac: expect-not-contains [[unresolved]]
-- unluac: expect-not-contains [[unluac error]]
local function opaque(value)
    return value
end

local value = opaque(7)
local function factory(tag)
    print("regress_298_event", tag)
    local function dependency(limit)
        local total = 0
        for index = 1, limit do
            total += index
        end
        return total
    end
    return function()
        return dependency(8) + value
    end
end

local first = factory("first")
local second = factory("second")
print("regress_298_result", first == second, first(), second())
