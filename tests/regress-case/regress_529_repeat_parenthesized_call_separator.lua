-- regress_529_repeat_parenthesized_call_separator: until 条件不能吸收下一条括号调用。
-- unluac: expect-ast-min [[repeat]] [[1]]
-- unluac: expect-contains [[repeat]]
-- unluac: expect-contains [[;]]
-- unluac: expect-contains [[(function(]]
-- unluac: expect-not-contains [[unluac error]]
local function run(limit)
    local object = { field = 0 }
    repeat
        object.field = object.field + 1
    until object.field >= limit;
    (function(value)
        assert(value.field == limit)
    end)(object)
    print("regress_529_repeat_parenthesized_call_separator", object.field)
end
run(1)
run(3)
