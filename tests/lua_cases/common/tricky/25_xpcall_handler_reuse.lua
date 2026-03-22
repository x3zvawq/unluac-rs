local function risky(kind)
    if kind == "ok" then
        return "safe", 12, 18
    end

    error("boom:" .. kind)
end

local function handler(err)
    return "handled<" .. (string.match(err, "boom:[^>]+") or err) .. ">"
end

local ok1, a1, b1, c1 = xpcall(function()
    return risky("ok")
end, handler)
local ok2, res2 = xpcall(function()
    return risky("bad")
end, handler)

print("xpcall", ok1, a1, b1, c1)
print("xpcall", ok2, res2)
