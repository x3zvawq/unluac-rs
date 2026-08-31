-- Decision synthesis must model Lua numeric equality across integer/float representations.

local function choose(value, fallback)
    local result
    if value == 1 then
        if value == 1.0 then
            result = false
        else
            result = fallback
        end
    else
        result = fallback
    end
    return result
end

assert(choose(1.0, "fallback") == false)
assert(choose(2, "fallback") == "fallback")
print("regress340", choose(1.0, "fallback"), choose(2, "fallback"))
