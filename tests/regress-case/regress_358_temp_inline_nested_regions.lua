-- regress_358_temp_inline_nested_regions: 必达 nested 可收回，条件区域与 table allocation 保留 producer
-- unluac: expect-contains [[lookup_result = 1 + source[key]]
-- unluac: expect-contains [[arithmetic_result = 1 + value()]]
-- unluac: expect-contains [[f()[1]()]]
-- unluac: expect-not-contains [[condition and f()]]
-- unluac: expect-not-contains [[{ source[key] }]]
-- unluac: expect-not-contains [[unluac error]]

source = { key = 41 }
key = "key"

local lookup = source[key]
lookup_result = 1 + lookup

hits = 0
function f()
    hits = hits + 1
    return { function() hits = hits + 1 end }
end

function value()
    hits = hits + 1
    return 41
end

local arithmetic = value()
arithmetic_result = 1 + arithmetic

local caller = f()
caller[1]()

condition = false
local eager = f()
selected = condition and eager

local field = source[key]
boxed = { field }

assert(lookup_result == 42 and arithmetic_result == 42 and hits == 4 and selected == false and boxed[1] == 41)
print("nested-regions", lookup_result, arithmetic_result, hits, selected, boxed[1])
