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

print("regress_277_boundary_alias_snapshot#1", run(false, true, false, false))
print("regress_277_boundary_alias_snapshot#2", run(true, false, true, false))
print("regress_277_boundary_alias_snapshot#3", run(false, false, false, false))
