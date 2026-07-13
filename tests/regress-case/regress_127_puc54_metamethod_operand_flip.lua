-- regress_127_puc54_metamethod_operand_flip#1: MMBINI/MMBINK 的 flip 必须保留源码操作数顺序
-- unluac: expect-not-contains [[unluac error]]
local function mark(name)
    return function(a, b)
        local av = type(a) == "number" and a or "-"
        local bv = type(b) == "number" and b or "-"
        return name .. ":" .. type(a) .. ":" .. type(b) .. ":" .. av .. ":" .. bv
    end
end

local x = setmetatable({}, {
    __add = mark("add"),
    __sub = mark("sub"),
    __mul = mark("mul"),
    __band = mark("band"),
    __shl = mark("shl"),
    __shr = mark("shr"),
})
local y = setmetatable({}, getmetatable(x))

print("regress_127_puc54_metamethod_operand_flip#1", 5 + x)
print("regress_127_puc54_metamethod_operand_flip#2", 300 + x)
print("regress_127_puc54_metamethod_operand_flip#3", 5 * x)
print("regress_127_puc54_metamethod_operand_flip#4", 5 & x)
print("regress_127_puc54_metamethod_operand_flip#5", x - 5)
print("regress_127_puc54_metamethod_operand_flip#6", x << -5)
print("regress_127_puc54_metamethod_operand_flip#7", 5 << x)
print("regress_127_puc54_metamethod_operand_flip#8", x >> -5)
print("regress_127_puc54_metamethod_operand_flip#9", x + y)
print("regress_127_puc54_metamethod_operand_flip#10", x << y)
