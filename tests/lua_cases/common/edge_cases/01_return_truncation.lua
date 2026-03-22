local function returns()
    return "A", "B", "C"
end

local values = { returns(), "tail", returns() }

print("ret", table.concat(values, ","))
