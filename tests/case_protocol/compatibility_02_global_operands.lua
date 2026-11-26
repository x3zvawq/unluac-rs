-- regress_136_luau_global_operands#1: GETGLOBAL/SETGLOBAL 必须按 A/C 协议解码
luau_global_operand = 8
assert(luau_global_operand == 8)
print("regress_136_luau_global_operands#1", luau_global_operand)
luau_global_neighbor = "neighbor"
luau_global_operand = luau_global_operand + 3
assert(luau_global_operand == 11 and luau_global_neighbor == "neighbor")
luau_global_operand = false
assert(luau_global_operand == false and luau_global_neighbor == "neighbor")
luau_global_operand = nil
assert(luau_global_operand == nil and luau_global_neighbor == "neighbor")
