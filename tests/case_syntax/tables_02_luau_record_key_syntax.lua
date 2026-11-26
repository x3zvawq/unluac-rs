-- Bare names would enable sequential-index allocation in this hash-only NEWTABLE.
local function named_growth(value)
    local result = { ["a"] = 1, ["b"] = nil, ["c"] = value, [1] = 42 }
    result.e = 5
    return result
end
for key, value in pairs(named_growth(7)) do
    print("named", key, value)
end

-- Later numeric growth observes the original hash placement too.
local function numeric_growth(value)
    local result = { ["a"] = 1, ["b"] = nil, ["c"] = value, [1] = 42 }
    result[2] = 7
    result[3] = 8
    return result
end
local result = numeric_growth(7)
for key, value in pairs(result) do
    print("numeric", key, value)
end
result[1] = nil
result[3] = nil
print("length", #result)

local function function_growth(value)
    local result = { ["a"] = 1, ["b"] = nil, ["c"] = value, [1] = 42 }
    result.e = function() return 5 end
    return result
end
for key, value in pairs(function_growth(7)) do
    if type(value) == "function" then value = value() end
    print("function", key, value)
end
