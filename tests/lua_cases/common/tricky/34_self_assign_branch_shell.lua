local log = {}

local function mark(tag, value)
    log[#log + 1] = tag
    return value
end

local a = "x"

if mark("m1", mark("m2", 1)) then
    a = a
else
    a = "z"
end

print("self-assign-branch", tostring(a), table.concat(log, ","))
