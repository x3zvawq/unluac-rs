local function make_mixer(seed, stride)
    local mask = ((seed << 2) | 0x35) ~ (stride & 0x0F)
    local history = {}

    return function(list)
        local acc = mask

        for i = 1, #list do
            local value = list[i]
            local mixed = (((value << (i % 3)) | acc) ~ (seed >> (i - 1))) & 0xFF

            if (mixed & 1) == 0 then
                acc = ((acc ~ mixed) << 1) & 0xFF
            else
                acc = ((acc | mixed) >> 1) ~ stride
            end

            history[#history + 1] = acc ~ i
        end

        return acc, history[#history - 1], history[#history]
    end
end

local run_a = make_mixer(0x2D, 0x13)
local run_b = make_mixer(0x19, 0x05)

print("bit-closure", run_a({ 3, 9, 12, 17 }))
print("bit-closure", run_b({ 8, 1, 14 }))
