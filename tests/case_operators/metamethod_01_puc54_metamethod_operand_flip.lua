-- regress_127_puc54_metamethod_operand_flip#1: MMBINI/MMBINK 的 flip 必须保留源码操作数顺序
-- unluac: expect-not-contains [[unluac error]]
-- unluac: expect-not-contains [[local r2_2 = p1_0 ..]]
-- unluac: expect-contains [[return p1_0 .. ":"]]
-- unluac: expect-ast-count [[function]] [[2]]
-- unluac: expect-ast-count [[if]] [[0]]
-- unluac: expect-ast-max [[local-binding]] [[6]]
-- type 的结果只供紧接的短路选择，不应留下 callee/result 的独立赋值包装。
-- unluac: expect-count [[type(p2_0) == "number" and p2_0 or "-"]] [[1]]
-- unluac: expect-count [[type(p2_1) == "number" and p2_1 or "-"]] [[1]]
local calls = 0
local function mark(name)
    return function(a, b)
        calls = calls + 1
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
assert(calls == 10)
assert(5 + x == "add:number:table:5:-")
assert(300 + x == "add:number:table:300:-")
assert(5 * x == "mul:number:table:5:-")
assert(5 & x == "band:number:table:5:-")
assert(x - 5 == "sub:table:number:-:5")
assert(x << -5 == "shl:table:number:-:-5")
assert(5 << x == "shl:number:table:5:-")
assert(x >> -5 == "shr:table:number:-:-5")
assert(x + y == "add:table:table:-:-")
assert(x << y == "shl:table:table:-:-")
assert(calls == 20)
