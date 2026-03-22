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

do
    local resource <close> = make_resource("res")
    log[#log + 1] = "body:" .. resource.name
end

print("close", table.concat(log, "|"))
