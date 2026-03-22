local function pair()
    return "x", "y"
end

local function join(a, b, c, d)
    return table.concat({ a, b, c, d }, ",")
end

local result = join(pair(), "mid", pair())
print("call-barrier", result)
