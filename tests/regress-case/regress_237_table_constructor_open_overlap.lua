-- regress_237_table_constructor_open_overlap: open list writes conditionally cover old suffix
-- unluac: expect-not-contains [[unluac error]]
-- unluac: expect-not-contains [[unresolved]]
local calls = 0

local function many()
    calls = calls + 1
    return "a", "b", "c"
end

local function none()
    calls = calls + 1
    return
end

local covered = { [2] = "old", "head", many() }
assert(calls == 1)
assert(#covered == 4)
assert(covered[1] == "head" and covered[2] == "a")
assert(covered[3] == "b" and covered[4] == "c")

local preserved = { [2] = "old", "head", none() }
assert(calls == 2)
assert(#preserved == 2)
assert(preserved[1] == "head" and preserved[2] == "old")

print("regress_237_table_constructor_open_overlap", "ok")
