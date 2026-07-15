-- regress_194_discarded_table_open_tail#1: 多赋值的多余 RHS 仍须完整求值 open table tail
-- unluac: expect-contains [[{ false, true,]]
-- unluac: expect-not-contains [[unluac error]]
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

print("regress_194_discarded_table_open_tail#1", run(), calls)
