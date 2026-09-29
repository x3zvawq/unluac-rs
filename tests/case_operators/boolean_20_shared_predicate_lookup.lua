-- 短路节点共享一次 CALL/GETTABLE 结果；吸收条件准备区不能把共享 Def 复制到各谓词。
-- unluac: expect-count [[.value]] [[3]]
-- unluac: expect-count [[().value]] [[3]]
-- unluac: expect-count [[local value = inspect().value]] [[3]] [[@debug=retained]]
-- unluac: expect-contains [[if value == value then]] [[@debug=retained]]
-- unluac: expect-not-contains [[unluac error]]
-- unluac: expect-ast-count [[function]] [[5]]
-- unluac: expect-ast-max [[local-binding]] [[12]]
-- unluac: expect-ast-max [[local-binding]] [[3]] [[@dialect=lua5.1]] [[@proto=5]]
-- unluac: expect-ast-max [[local-binding]] [[3]] [[@dialect=lua5.2]] [[@proto=5]]
-- unluac: expect-ast-max [[local-binding]] [[3]] [[@dialect=lua5.3]] [[@proto=5]]
-- unluac: expect-ast-max [[local-binding]] [[3]] [[@dialect=lua5.4]] [[@proto=5]]
-- unluac: expect-ast-max [[local-binding]] [[3]] [[@dialect=lua5.5]] [[@proto=5]]
-- unluac: expect-ast-max [[local-binding]] [[3]] [[@dialect=luajit]] [[@proto=1]]
-- unluac: expect-ast-max [[local-binding]] [[3]] [[@dialect=luau]] [[@proto=5]]
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
-- 同值比较不是恒真：NaN 仍须保留原比较，且每次只读取一次字段。
result = 0 / 0
assert(not check(true))
assert(not check_same_operand(true))
assert(calls == 6 and reads == 6)
result = nil
assert(not check(true) and check_same_operand(true))
assert(calls == 8 and reads == 8)
result = false
assert(not check(true) and check_same_operand(true))
assert(calls == 10 and reads == 10)
assert(not check(nil) and not check_same_operand(nil))
assert(calls == 10 and reads == 10)
result = 7
assert(check(0) and check(""))
assert(select("#", check(false)) == 1)
assert(calls == 12 and reads == 12)
result = {}
assert(check_same_operand(true) and not check(true))
assert(calls == 14 and reads == 14)

-- 值决策也要沿透明 COPY 保留共享 producer；谓词与结果计算各读一次同一个快照。
local function select_shared(enabled)
    local out = 0
    if enabled then
        local value = inspect().value
        local copied = value
        if copied == 3 then out = copied else out = copied + 1 end
    end
    return out
end
result = 7
assert(select_shared(true) == 8 and calls == 15 and reads == 15)
result = 3
assert(select_shared(true) == 3 and calls == 16 and reads == 16)
assert(select_shared(false) == 0 and calls == 16 and reads == 16)
