-- regress_254_table_constructor_handoff_snapshot#1: 构造器调用不能提前快照后续 handoff base
local target = { name = "old" }

local function make_value()
    target = { name = "new" }
    return "value"
end

local result = { make_value() }
target.value = result

print("regress_254_table_constructor_handoff_snapshot#1", target.name, target.value[1])
