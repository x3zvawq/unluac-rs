-- regress_192_luau_open_pack_callee_move#1: open producer 后的单 callee Move 不阻断 owner
-- unluac: expect-contains [[bit32.bor]]
-- unluac: expect-not-contains [[unresolved]]
-- unluac: expect-not-contains [[unluac error]]

local function nested()
    local op = bit32.bor
    return op(op(-1, -2))
end

local function prefixed()
    local op = bit32.bor
    return op(1, op(-1, -2))
end

print("regress_192_luau_open_pack_callee_move#1", nested(), prefixed())
