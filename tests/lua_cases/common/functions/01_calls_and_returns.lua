local function pair(a, b)
    return a + b, a * b
end

local sum, product = pair(4, 6)
print("call", sum, product)
