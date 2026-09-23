-- 整数和浮点数值相等不授权合并两次原比较；返回值仍须保留数值表示。
-- unluac: expect-ast-count [[if]] [[0]] [[@proto=1]]
-- 两个比较仍各自存在，只把共同 fallback 出口收回短路表达式。
-- unluac: expect-contains [[return (p1_0 ~= 1 or p1_0 ~= 1.0) and p1_1]]
-- 非折叠算术仍在原参数槽求值，不留下 callee 快照污染后续声明前缀。
-- unluac: expect-contains [[assert(r0_0(0 / 0, "nan") == "nan")]]
-- unluac: expect-ast-count [[local-binding]] [[2]] [[@proto=0]]

local function choose(value, fallback)
    local result
    if value == 1 then
        if value == 1.0 then
            result = false
        else
            result = fallback
        end
    else
        result = fallback
    end
    return result
end

assert(choose(1.0, "fallback") == false)
assert(choose(2, "fallback") == "fallback")
assert(choose(1.0, nil) == false)
assert(choose(nil, nil) == nil)
assert(choose(2, false) == false)
assert(choose(0 / 0, "nan") == "nan")

local function preserve_numeric_representation(value)
    if value and 1 then
        return (value == 1) and 1
    else
        return value
    end
end

assert(math.type(preserve_numeric_representation(1.0)) == "integer")
print(
    "regress340",
    choose(1.0, "fallback"),
    choose(2, "fallback"),
    math.type(preserve_numeric_representation(1.0))
)
