-- 不同编译器可能交换相等比较的操作数，但三个原比较都必须保留。
-- 原函数三个比较及下方四个结果/宽度断言均须保留。
-- unluac: expect-count [[ == ]] [[7]]

local function compare_mismatched_primitives()
    return nil == false, true == "true", 7 == "7"
end

local nil_boolean, boolean_string, number_string = compare_mismatched_primitives()
assert(not nil_boolean and not boolean_string and not number_string)
-- 三个 false 都必须实际返回；Lua 中 nil 同样是假，不能只检查真假性。
assert(nil_boolean == false and boolean_string == false and number_string == false)
assert(select("#", compare_mismatched_primitives()) == 3)

return nil_boolean, boolean_string, number_string
