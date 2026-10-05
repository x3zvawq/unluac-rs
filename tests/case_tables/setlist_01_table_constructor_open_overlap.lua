-- regress_237_table_constructor_open_overlap: open list writes conditionally cover old suffix
-- unluac: expect-not-contains [[unluac error]]
-- unluac: expect-not-contains [[unresolved]]
-- unluac: expect-ast-count [[table-constructor]] [[2]] [[@proto=0]]
-- 两个旧字段与两个开放尾均留在构造器内，不拆出写回或调用结果的临时绑定。
-- unluac: expect-ast-max [[local-binding]] [[5]] [[@proto=0]]
-- unluac: expect-ast-count [[table-record-field]] [[2]] [[@proto=0]]
-- unluac: expect-ast-count [[table-list-field]] [[4]] [[@proto=0]]
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
