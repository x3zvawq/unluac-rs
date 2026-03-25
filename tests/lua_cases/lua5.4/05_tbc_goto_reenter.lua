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

local turn = 1

do
    local outer <close> = make_resource("outer")

    ::again::
    do
        local inner <close> = make_resource("inner:" .. turn)
        if turn < 3 then
            turn = turn + 1
            goto again
        end

        log[#log + 1] = outer.name .. "+" .. inner.name
    end
end

print(table.concat(log, "|"))
