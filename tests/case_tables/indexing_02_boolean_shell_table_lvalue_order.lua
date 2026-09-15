-- regress_249_boolean_shell_table_lvalue_order: 条件先于所选 arm 的 table 地址求值
-- unluac: expect-contains [[if]]

local first = {}
local second = {}
local holder = { target = first }

local function cond()
    holder.target = second
    return true
end

if cond() then
    holder.target.value = true
else
    holder.target.value = false
end

assert(first.value == nil)
assert(second.value == true)
print("regress_249_boolean_shell_table_lvalue_order")
