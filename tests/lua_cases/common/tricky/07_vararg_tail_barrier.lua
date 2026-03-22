local unpack_fn = table.unpack or unpack

local function vararg_test(...)
    local args = { ... }

    local function inner(...)
        return "data", ...
    end

    return inner(unpack_fn(args))
end

local function wrap(...)
    return { "start", vararg_test(...), "finish" }
end

local result = wrap("x", "y")
print("vararg-tricky", table.concat(result, ","))
