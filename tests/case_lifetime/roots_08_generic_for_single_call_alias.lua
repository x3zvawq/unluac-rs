-- regress_395_generic_for_single_call_alias: iterator 工厂的独立根必须保留到循环之后。
-- 循环体中的调用可能清空全局来源；只保留 dispatch iterator 不能替代其工厂根。
-- unluac: expect-ast-count [[generic-for]] [[2]]
-- unluac: expect-ast-count [[local-binding]] [[12]]
-- unluac: expect-ast-count [[function]] [[2]]

local iterator = ipairs
local values = { "one", "two" }
for index, value in iterator(values) do
    print(index, value)
end

-- unluac: expect-contains [[= ipairs]]
-- unluac: expect-not-contains [[in ipairs(]]

-- 可收集的工厂与 dispatch 函数分离；工厂来源被清空后，只剩循环外的别名保活。
local weak = setmetatable({}, { __mode = "v" })
local function exercise()
    local marker = {}
    local factory = function(items)
        assert(marker ~= nil)
        return iterator(items)
    end
    weak.factory = factory
    local alias = factory
    factory = nil
    local visits = 0
    for index, value in alias(values) do
        collectgarbage("collect")
        collectgarbage("collect")
        assert(weak.factory ~= nil, "factory root lost inside loop")
        assert(values[index] == value)
        visits = visits + 1
    end
    assert(visits == 2)
end
exercise()
collectgarbage("collect")
collectgarbage("collect")
assert(weak.factory == nil, "factory root outlived frame")
