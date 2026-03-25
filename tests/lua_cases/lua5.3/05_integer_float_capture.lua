local function factory(seed)
    local base_int = seed * 9 + 7
    local base_float = seed / 3 + 0.625

    return function(delta)
        local left = (base_int + delta * 5) // 4
        local right = ((base_int << 1) ~ delta) & 0x7F
        local wave = base_float + delta / 8

        if (right & 0x01) == 1 then
            base_int = (base_int ~ right) + left
            base_float = wave / 2.5
        else
            base_int = (base_int | right) - left
            base_float = wave * 1.75
        end

        return base_int, base_float, right // 3, wave
    end
end

local f = factory(11)
print("capture-mix", f(3))
print("capture-mix", f(8))
print("capture-mix", f(5))
