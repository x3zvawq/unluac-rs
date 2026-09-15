-- regress_191_vararg_open_pack_setup#1: VarArg open tail 可跨 callee setup
-- unluac: expect-contains [[...]]
-- unluac: expect-not-contains [[unresolved]]
-- unluac: expect-not-contains [[unluac error]]

local function direct(...)
    local abs = math.abs
    return abs(...)
end

local abs = math.abs
local function captured(...)
    return abs(...)
end

local direct_result, captured_result = direct(-5), captured(-6)
assert(direct_result == 5 and captured_result == 6)
print("regress_191_vararg_open_pack_setup#1", direct_result, captured_result)
