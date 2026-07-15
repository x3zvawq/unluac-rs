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

print("regress_191_vararg_open_pack_setup#1", direct(-5), captured(-6))
