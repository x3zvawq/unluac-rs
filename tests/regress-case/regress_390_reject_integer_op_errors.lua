local function reject_floor_zero()
    local numerator = 1
    local zero = 0
    local unused = numerator // zero
    if 1 == 1 then
        print("unreachable-after-floor-zero")
    else
        print(unused)
    end
end

local function reject_mod_zero()
    local numerator = 1
    local zero = 0
    local unused = numerator % zero
    if 1 == 1 then
        print("unreachable-after-mod-zero")
    else
        print(unused)
    end
end

local function reject_float_bit_not()
    local value = 1.5
    local unused = ~value
    if 1 == 1 then
        print("unreachable-after-float-bit-not")
    else
        print(unused)
    end
end

assert(not pcall(reject_floor_zero))
assert(not pcall(reject_mod_zero))
assert(not pcall(reject_float_bit_not))
