-- Shared flow events must distinguish loop initialization, backedges and terminal reads.
local function branch_exit(flag)
    local state = 10
    local result = state + 3
    if false then
        print("unreachable", state)
    end
    if flag then
        return result
    end
    state = result
    return state
end
print("branch-exit", branch_exit(false), branch_exit(true))

local function parallel_exit(flag)
    local state = 7
    local result = state + 2
    if flag then
        return state, result
    end
    state, result = result, 19
    return state, result
end
print("parallel-old", parallel_exit(true))
print("parallel-new", parallel_exit(false))

local function loops(limit, stop)
    local state = 3
    for i = 1, limit do
        local result = state + i
        repeat
            if i == stop then
                break
            end
            result = result + 2
        until true
        state = result
        if i == stop then
            break
        end
    end
    return state
end
print("loops", loops(0, 2), loops(4, 2), loops(4, 0))

local factory_calls = 0
local function factory(limit, initial)
    factory_calls = factory_calls + 1
    local i = 0
    return function()
        i = i + 1
        if i <= limit then
            return i, initial + i
        end
    end
end
local function generic(limit, stop)
    local state = 5
    for i, value in factory(limit, state) do
        local result = state + value
        if i == stop then
            return result, state
        end
        state = result
    end
    return state, state
end
print("generic-empty", generic(0, 0))
print("generic-complete", generic(3, 0))
print("generic-return", generic(3, 2))
print("factory-calls", factory_calls)

local function latch(limit)
    local state = 0
    repeat
        local result = state + 1
        state = result
    until state >= limit
    return state
end
print("latch", latch(0), latch(3))
