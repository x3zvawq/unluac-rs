local function return_truncation(...)
    local t = { ..., "barrier", ... }
    local a, b, c = string.find("hello", "ll"), "extra", string.find("world", "or")
    return t, a, b, c
end

local t, a, b, c = return_truncation("x", "y")
print("retbarrier", table.concat(t, ","), a, b, c)
