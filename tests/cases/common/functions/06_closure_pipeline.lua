local function make_pipeline(seed)
    local current = seed

    return function(delta)
        current = current + delta

        return function(scale)
            current = current * scale
            return current
        end
    end
end

local pipeline = make_pipeline(2)
print("pipeline", pipeline(3)(4), pipeline(1)(2))
