-- regress_134_negative_literal_power#1: 负数字面量作为幂底数必须保留括号
-- 原闭包声明低于 CALL 准备槽；数值括号合同不要求把它改成 IIFE。
-- unluac: expect-ast-count [[local-function]] [[1]] [[@proto=0]]
-- unluac: expect-ast-count [[local-binding]] [[4]] [[@proto=0]]
-- unluac: expect-contains [[(-2) ^]]
-- unluac: expect-contains [[(-2.5) ^]]
local function powers(exponent)
    return (-2) ^ exponent, (-2.5) ^ exponent, (-0.0) ^ exponent
end

local integer, number, negative_zero = powers(2)
assert(integer == 4 and number == 6.25 and 1 / negative_zero == math.huge)
print("regress_134_negative_literal_power#1", integer, number, 1 / negative_zero)
