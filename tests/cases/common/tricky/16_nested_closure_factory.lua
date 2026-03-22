local function factory(seed)
    local offset = seed

    return function(step)
        local base = offset + step

        return function(mult)
            offset = base + mult
            return offset, base * mult
        end
    end
end

local stage1 = factory(2)
local stage2 = stage1(3)
print("nested-closure", stage2(4))
print("nested-closure", stage1(1)(2))
