-- Both decision leaves and the merged write must use the live generic-for binding.
-- unluac: expect-ast-min [[generic-for]] [[1]]
local function inspect(input)
    for key, value in pairs({ item = input }) do
        if type(value) == "function" then value = value() end
        print(key, type(value), value)
    end
end
inspect(function() return 7 end)
inspect(9)

local function rename(input)
    for key, value in pairs({ item = input }) do
        if value then value = "changed" end
        print(key, value)
    end
end
rename(true)
rename(false)

-- The header's ordinary write also targets the loop binding, not its SSA temp.
local function increment(enabled)
    for _, value in ipairs({ 3 }) do
        value = value + 1
        if enabled then value = value * 2 end
        print("increment", value)
    end
end
increment(true)
increment(false)
