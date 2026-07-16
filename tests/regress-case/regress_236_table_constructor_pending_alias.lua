-- regress_236_table_constructor_pending_alias: future integer fields do not cross aliasing writes
-- unluac: expect-not-contains [[unluac error]]
-- unluac: expect-not-contains [[unresolved]]
local duplicate = {}
duplicate[2] = "first"
duplicate[2] = "second"
duplicate[1] = "one"
assert(duplicate[1] == "one" and duplicate[2] == "second")

local numeric = {}
numeric[2] = "integer"
numeric[2.0] = "float"
numeric[1] = "one"
assert(numeric[1] == "one" and numeric[2] == "float")

local function build(key)
    local result = {}
    result[2] = "first"
    result[key] = "second"
    result[1] = "one"
    return result
end

local aliased = build(2)
local distinct = build(3)
assert(aliased[2] == "second")
assert(distinct[1] == "one" and distinct[2] == "first" and distinct[3] == "second")

local mixed = {
    [0] = "zero",
    "one",
    [3] = "three",
    [2] = "two",
    key = "value",
    [false] = "false-key",
    [2] = "two-final",
}
assert(mixed[0] == "zero" and mixed[1] == "one")
assert(mixed[2] == "two-final" and mixed[3] == "three")
assert(mixed.key == "value" and mixed[false] == "false-key")

print("regress_236_table_constructor_pending_alias", "ok")
