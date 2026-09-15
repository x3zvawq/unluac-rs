-- regress_277_boundary_alias_snapshot: goto边界复制不把跨更新时点的快照并成同一状态
-- unluac: expect-not-contains [[unresolved]]
-- unluac: expect-not-contains [[unluac error]]
local function run(entry, a, b, cycle)
    local value, snapshot, copied = 0, -1, -2
    if entry then
        goto second
    end

    ::first::
    if a then
        snapshot = value
        goto done
    end
    value = value + 1

    ::second::
    if b then
        copied = snapshot
        goto done
    end
    value = value + 10
    if cycle then
        goto first
    end

    ::done::
    return value, snapshot, copied
end

local a1, b1, c1 = run(false, true, false, false)
local a2, b2, c2 = run(true, false, true, false)
local a3, b3, c3 = run(false, false, false, false)
assert(a1 == 0 and b1 == 0 and c1 == -2)
assert(a2 == 0 and b2 == -1 and c2 == -1)
assert(a3 == 11 and b3 == -1 and c3 == -2)
print("regress_277_boundary_alias_snapshot#1", a1, b1, c1)
print("regress_277_boundary_alias_snapshot#2", a2, b2, c2)
print("regress_277_boundary_alias_snapshot#3", a3, b3, c3)
