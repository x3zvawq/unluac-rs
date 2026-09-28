-- regress_358_temp_inline_nested_regions: 必达 nested 可收回，条件区域与 table allocation 保留 producer
-- lookup 接收者的物理覆盖链由 regress_464 的 GC 观察验证，不要求跨 owner 内联。
-- unluac: expect-contains [[lookup_result = 1 +]]
-- unluac: expect-contains [[arithmetic_result = 1 + value()]]
-- 原始嵌套调用应保持调用链；独立 owner 则必须活到被调用函数中的 GC 观察。
-- unluac: expect-count [[()[1]()]] [[1]]
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

-- 两种原帧在 callee 内的观察不同，不能按值流等价合并。
do
    local weak = setmetatable({}, { __mode = "v" })
    local expected_alive = true
    local function make()
        local result = { function()
            collectgarbage("collect")
            assert((weak[1] ~= nil) == expected_alive)
        end }
        weak[1] = result
        return result
    end
    local function retained()
        local owner = make()
        owner[1]()
    end
    local function nested()
        make()[1]()
    end
    retained()
    expected_alive = false
    nested()
end
