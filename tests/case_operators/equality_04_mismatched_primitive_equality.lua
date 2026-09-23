-- 不同编译器可能交换相等比较的操作数，但三个原比较都必须保留。
-- unluac: expect-count [[ == ]] [[3]]

local function compare_mismatched_primitives()
    return nil == false, true == "true", 7 == "7"
end

local nil_boolean, boolean_string, number_string = compare_mismatched_primitives()
assert(not nil_boolean and not boolean_string and not number_string)

return nil_boolean, boolean_string, number_string
