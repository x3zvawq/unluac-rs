local function make_filter(seed)
    local state = (~seed) & 0xFF

    return function(values)
        local total = 0

        for i = 1, #values do
            local flipped = (~values[i]) & 0xFF

            if (flipped & 0x03) == 0 then
                state = ((state << 1) ~ flipped) & 0xFF
            else
                state = ((state >> 1) | flipped) ~ i
            end

            total = total + (state // (i + 1))
        end

        return state, total, (~state) & 0xFF
    end
end

local f = make_filter(0x2D)
print("bnot-pipeline", f({ 3, 8, 12, 19 }))
print("bnot-pipeline", f({ 5, 7, 11 }))
