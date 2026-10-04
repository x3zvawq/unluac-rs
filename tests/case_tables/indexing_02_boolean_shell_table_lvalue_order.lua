-- unluac: expect-ast-count [[if]] [[2]]
-- unluac: expect-ast-count [[function]] [[1]]
-- unluac: expect-ast-count [[table-constructor]] [[3]]
-- unluac: expect-ast-max [[local-binding]] [[5]]
-- regress_249_boolean_shell_table_lvalue_order: 条件先于所选 arm 的 table 地址求值
-- unluac: expect-contains [[if]]

local first = {}
local second = {}
local holder = { target = first }

local calls = 0
local function cond(value)
    calls = calls + 1
    holder.target = second
    return value
end

if cond(true) then
    holder.target.value = true
else
    holder.target.value = false
end

assert(first.value == nil)
assert(second.value == true and calls == 1)
print("regress_249_boolean_shell_table_lvalue_order")

-- 假分支也须在条件完成后读取目标；条件不能重复求值。
holder.target = first
second.value = nil
if cond(false) then
    holder.target.value = true
else
    holder.target.value = false
end
assert(first.value == nil)
assert(second.value == false and calls == 2)
