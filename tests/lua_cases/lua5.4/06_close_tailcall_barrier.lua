local log = {}

local function make_resource(name)
    return setmetatable({
        name = name,
    }, {
        __close = function(self, err)
            log[#log + 1] = self.name .. ":" .. tostring(err == nil)
        end,
    })
end

local function invoke(fn, ...)
    return fn(...)
end

local function finalize(tag, mode, ...)
    local resource <close> = make_resource(tag)

    local function build(...)
        local parts = { ... }
        parts[#parts + 1] = resource.name
        return table.concat(parts, ":")
    end

    if mode == "tail" then
        return invoke(build, ...)
    end

    return build(...)
end

print(finalize("alpha", "tail", "x", "y"))
print(finalize("beta", "plain", "m"))
print(table.concat(log, "|"))
