-- regress_254_table_constructor_handoff_snapshot#1: 构造器调用不能提前快照后续 handoff base
-- unluac: expect-ast-count [[table-list-field]] [[1]]
-- unluac: expect-ast-max [[table-constructor]] [[3]]
local target = { name = "old" }

local function make_value()
    target = { name = "new" }
    return "value"
end

local result = { make_value() }
target.value = result

assert(target.name == "new" and target.value[1] == "value")
print("regress_254_table_constructor_handoff_snapshot#1", target.name, target.value[1])
