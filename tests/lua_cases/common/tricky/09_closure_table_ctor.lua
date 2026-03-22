local function make_counter()
    local state = {
        current = 1,
    }

    return function(step)
        state.current = state.current + (step or 1)
        return state.current
    end
end

local counter = make_counter()
print("closure-table", counter(), counter(2), counter())
