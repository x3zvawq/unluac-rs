local function values()
    return 10, 20, 30
end

local a, b, c = 1, 2, 3
a, b, c = b, c, values()
print("assign-rot", a, b, c)

a, b, c = values(), a, b
print("assign-rot", a, b, c)
