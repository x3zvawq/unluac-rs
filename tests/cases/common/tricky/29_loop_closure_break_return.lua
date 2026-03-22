local function collect(limit)
    local funcs = {}
    local i = 0

    while i < limit do
        i = i + 1
        local captured = i * 5

        funcs[#funcs + 1] = function(extra)
            return captured + extra, i
        end

        if i == 3 then
            break
        end
    end

    return funcs, i
end

local funcs, final_i = collect(6)
local a, b = funcs[1](2)
local c, d = funcs[3](4)

print("loop-closure", a, b, c, d, final_i, funcs[4] == nil)
