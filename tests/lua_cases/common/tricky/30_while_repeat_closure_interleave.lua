local function run()
    local i = 0
    local out = {}

    while i < 3 do
        i = i + 1
        local base = i

        repeat
            out[#out + 1] = function(delta)
                return base + delta, i
            end
            base = base + 10
        until base > i + 10
    end

    return out
end

local funcs = run()
local a1, a2 = funcs[1](1)
local b1, b2 = funcs[2](2)
local c1, c2 = funcs[3](3)

print("while-repeat", a1, a2, b1, b2, c1, c2)
