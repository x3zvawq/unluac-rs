local function fail()
    error("oops")
end

local function handler(err)
    return "handled:" .. ((string.match(err, "oops") and "oops") or err)
end

local ok, res = xpcall(fail, handler)
print("xpcall", ok, res)
