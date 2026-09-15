-- Decision synthesis must model Lua numeric equality across integer/float representations.
-- unluac: expect-ast-max [[if]] [[0]] [[@proto=1]]

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

local function preserve_numeric_representation(value)
    if value and 1 then
        return (value == 1) and 1
    else
        return value
    end
end

assert(math.type(preserve_numeric_representation(1.0)) == "integer")
print(
    "regress340",
    choose(1.0, "fallback"),
    choose(2, "fallback"),
    math.type(preserve_numeric_representation(1.0))
)
