local function analyze(values)
    local score = 0
    local frac = 0.0

    for i = 1, #values do
        local value = values[i]
        local floor = (value * 3 + i) // 2
        local ratio = (value * 3 + i) / 2
        local mod = (floor + i) % 5

        if mod == 0 or (ratio - floor) > 0.4 then
            score = score + floor - mod
            frac = frac + (ratio / (i + 1))
        else
            score = score - ((value + mod) // 3)
            frac = frac + ((value / 5) - (floor / 7))
        end
    end

    return score, frac, score // 3, frac / #values
end

local a, b, c, d = analyze({ 5, 8, 13, 21, 34 })
print("idiv-float", a, b, c, d)
