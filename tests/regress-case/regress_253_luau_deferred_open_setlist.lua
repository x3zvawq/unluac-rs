-- regress_253_luau_deferred_open_setlist#1: 保留 open SETLIST 前的短路 producer
-- unluac: expect-contains [[return { table.unpack(]]
-- unluac: expect-contains [[.values or {}]]
-- unluac: expect-not-contains [[unluac error]]
-- unluac: expect-not-contains [[unresolved]]
local function build(loaded)
    return { table.unpack(loaded.values or {}) }
end

local values = build({ values = { "a", "b" } })
print("regress_253_luau_deferred_open_setlist#1", #values, values[1], values[2])
