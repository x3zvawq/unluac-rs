-- regress_134_negative_literal_power#1: 负数字面量作为幂底数必须保留括号
-- unluac: expect-contains [[(-2) ^]]
-- unluac: expect-contains [[(-2.5) ^]]
local function powers(exponent)
    return (-2) ^ exponent, (-2.5) ^ exponent, (-0.0) ^ exponent
end

local integer, number, negative_zero = powers(2)
print("regress_134_negative_literal_power#1", integer, number, 1 / negative_zero)
