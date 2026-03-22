local function factorial(n)
    local function inner(x, acc)
        if x == 0 then
            return acc
        end

        return inner(x - 1, acc * x)
    end

    return inner(n, 1)
end

print("rec", factorial(5), factorial(3))
