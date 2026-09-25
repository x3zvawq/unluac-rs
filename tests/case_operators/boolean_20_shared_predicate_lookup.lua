-- 短路节点共享一次 CALL/GETTABLE 结果；吸收条件准备区不能把共享 Def 复制到各谓词。
-- unluac: expect-count [[.value]] [[2]]
-- unluac: expect-count [[().value]] [[2]]
-- unluac: expect-count [[local value = inspect().value]] [[2]] [[@debug=retained]]
-- unluac: expect-contains [[if value == value then]] [[@debug=retained]]
-- unluac: expect-not-contains [[unluac error]]
local calls = 0
local reads = 0
local result = 7
local function inspect()
    calls = calls + 1
    return setmetatable({}, {
        __index = function(_, key)
            assert(key == "value")
            reads = reads + 1
            return result
        end,
    })
end
local function check(enabled)
    if enabled then
        local value = inspect().value
        if value == 3 or value == 7 then
            return true
        end
    end
    return false
end
local function check_same_operand(enabled)
    if enabled then
        local value = inspect().value
        if value == value then
            return true
        end
    end
    return false
end
assert(check(true))
assert(calls == 1 and reads == 1)
result = 3
assert(check(true))
assert(calls == 2 and reads == 2)
result = 9
assert(not check(true))
assert(calls == 3 and reads == 3)
assert(not check(false))
assert(calls == 3 and reads == 3)
assert(check_same_operand(true))
assert(calls == 4 and reads == 4)
assert(not check_same_operand(false))
assert(calls == 4 and reads == 4)
print("boolean_20_shared_predicate_lookup", calls, reads)
