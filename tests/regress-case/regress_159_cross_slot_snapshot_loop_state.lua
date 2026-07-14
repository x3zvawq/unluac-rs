-- regress_159_cross_slot_snapshot_loop_state#1: 不同 home slot 的 move 保留赋值时快照
-- unluac: expect-not-contains [[unresolved]]
-- unluac: expect-not-contains [[unluac error]]
local current = 1
local original = current
while current > 0 do
    current = current - 1
end

local function read()
    return current, original
end

print("regress_159_cross_slot_snapshot_loop_state#1", read())
