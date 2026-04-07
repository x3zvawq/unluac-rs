local log = {}

local function mark(tag, value)
    log[#log + 1] = tag
    return value
end

local a = "x"
local d = "y"

if mark("m2", 1) or d then
    a = a
else
    a = d
end

print("impure-or-branch", tostring(a), tostring(d), table.concat(log, ","))
