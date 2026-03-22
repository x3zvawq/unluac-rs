local function may_fail(x)
    if x < 0 then
        error("neg:" .. x)
    end

    return x * 2
end

local ok1, res1 = pcall(may_fail, 2)
local ok2, res2 = pcall(may_fail, -3)

print("pcall", ok1, res1, ok2, string.match(res2, "neg:%-3") ~= nil)
