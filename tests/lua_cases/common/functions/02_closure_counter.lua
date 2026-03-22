local function make_counter(start)
    local value = start

    return function(step)
        value = value + (step or 1)
        return value
    end
end

local counter = make_counter(10)
print("closure", counter(), counter(2), counter())
