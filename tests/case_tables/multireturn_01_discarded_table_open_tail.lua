-- regress_194_discarded_table_open_tail#1: 多赋值的多余 RHS 仍须完整求值 open table tail
-- unluac: expect-contains [[{ false, true,]]
-- unluac: expect-not-contains [[unluac error]]
-- 丢弃的 RHS 仍完整求值，但不要为副本、true 和构造结果分别建立接棒声明。
-- unluac: expect-ast-max [[local-binding]] [[6]]
-- unluac: expect-ast-count [[table-constructor]] [[1]]
local calls = 0

local function pack()
    calls = calls + 1
    return 1, 2, 3
end

local function run()
    local first = 2
    first = first, true, {false, true, pack()}
    return first
end

local result = run()
assert(result == 2 and calls == 1)
print("regress_194_discarded_table_open_tail#1", result, calls)
