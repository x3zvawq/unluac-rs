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

local function consume(mode)
    local out = {}

    do
        local first <close> = make_resource("first:" .. mode)
        out[#out + 1] = first.name

        while true do
            local second <close> = make_resource("second:" .. mode)
            out[#out + 1] = second.name

            if mode == "return" then
                return out
            end

            if mode == "break" then
                break
            end

            out[#out + 1] = first.name .. "+" .. second.name
            break
        end

        out[#out + 1] = "after:" .. first.name
    end

    return out
end

print(table.concat(consume("break"), ","))
print(table.concat(consume("return"), ","))
print(table.concat(log, "|"))
