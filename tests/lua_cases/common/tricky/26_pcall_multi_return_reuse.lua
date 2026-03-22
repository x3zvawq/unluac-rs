local function risky(flag, value)
    if flag then
        return value, value + 1, value + 2
    end

    error("bad:" .. value)
end

local function summarize(...)
    return table.concat({ ... }, ",")
end

local ok1, a1, b1, c1 = pcall(risky, true, 7)
local ok2, err2 = pcall(risky, false, 5)

print("pcall-ret", ok1, summarize(a1, b1, c1))
print("pcall-ret", ok2, string.match(err2, "bad:5") ~= nil)
