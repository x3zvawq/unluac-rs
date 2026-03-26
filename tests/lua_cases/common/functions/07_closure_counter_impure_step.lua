local function make_counter(start)
    local value = start
    local step_source = {
        index = 0,
        values = {
            [1] = nil,
            [2] = 3,
            [3] = nil,
            [4] = 2,
        },
    }

    function step_source:next()
        self.index = self.index + 1
        return self.values[self.index]
    end

    return function()
        value = value + (step_source:next() or 1)
        return value
    end
end

local counter = make_counter(10)
print("closure-impure", counter(), counter(), counter(), counter())
