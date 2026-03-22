local unpack_fn = table.unpack or unpack

local function forward(...)
    local args = { ... }

    local function inner(...)
        return "head", ...
    end

    return inner(unpack_fn(args))
end

print("vararg", forward("x", "y", "z"))
