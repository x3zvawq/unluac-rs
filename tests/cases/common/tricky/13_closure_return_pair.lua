local function closure_test(start_val)
    local counter = start_val

    local function increment(step)
        counter = counter + (step or 1)
        return counter
    end

    local function multiplier(m)
        return counter * m
    end

    return increment, multiplier
end

local inc, mul = closure_test(2)
print("closure-pair", inc(), mul(3), inc(4), mul(2))
