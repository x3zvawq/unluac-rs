-- regress_159_cross_slot_snapshot_loop_state#1: 不同 home slot 的 move 保留赋值时快照
-- unluac: expect-not-contains [[unresolved]]
-- unluac: expect-not-contains [[unluac error]]
-- unluac: expect-ast-count [[while]] [[1]]
-- unluac: expect-ast-count [[function]] [[1]]
-- unluac: expect-ast-max [[local-binding]] [[7]]
local current = 1
local original = current
local visits = 0
while current > 0 do
    visits = visits + 1
    current = current - 1
end

local function read()
    return current, original
end

assert(current == 0 and original == 1)
local first, second, extra = read()
assert(first == 0 and second == 1 and extra == nil and visits == 1)
current = 5
first, second, extra = read()
assert(first == 5 and second == 1 and extra == nil)
print("regress_159_cross_slot_snapshot_loop_state#1", read())
