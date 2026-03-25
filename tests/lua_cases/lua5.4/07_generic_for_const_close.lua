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

local function list_iter(values)
    local index = 0
    return function()
        index = index + 1
        if index <= #values then
            return index, values[index], #values - index
        end
    end
end

local out = {}

for index, value, remaining in list_iter({ "aa", "bbb", "c" }) do
    local prefix <const> = value .. ":" .. index
    do
        local resource <close> = make_resource(prefix)
        if remaining % 2 == 0 then
            out[#out + 1] = resource.name .. ":even"
        else
            out[#out + 1] = resource.name .. ":odd"
        end
    end
end

print(table.concat(out, "|"))
print(table.concat(log, "|"))
