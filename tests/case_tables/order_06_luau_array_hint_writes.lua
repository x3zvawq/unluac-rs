-- 空表的数组容量提示不把乱序独立字段写变成构造器；CALL 保留在原写回处。
-- unluac: expect-ast-max [[local-binding]] [[3]] [[@proto=0]]
local value = 20
local function mutate()
    value = 30
    return 10
end
local result = {}
result[2] = value
result[1] = mutate()
assert(result[1] == 10)
assert(result[2] == 20)
assert(value == 30)
print("array hint writes", result[1], result[2], value)
