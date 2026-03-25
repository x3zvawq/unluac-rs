local handlers = {
    [0] = function(state, value)
        return ((state << 1) ~ value) & 0xFF
    end,
    [1] = function(state, value)
        return ((state >> 1) | (value << 2)) ~ 0x33
    end,
    [2] = function(state, value)
        return state + ((value * 5) // 2) - (value % 3)
    end,
}

local state = 0x41
local log = {}
local values = { 6, 11, 4, 15, 9, 2 }
local i = 1

while i <= #values do
    local value = values[i]
    local kind = (value ~ i) & 0x03
    local handler = handlers[kind] or handlers[2]

    state = handler(state, value)

    if (state & 0x07) == 0 then
        log[#log + 1] = state // (i + 1)
    else
        log[#log + 1] = (state % 17) + (value / 4)
    end

    if state > 180 and i < #values then
        values[#values + 1] = ((state >> 2) ~ value) & 0x1F
    end

    i = i + 1
end

print("dispatch53", state, log[1], log[3], log[#log], #values)
