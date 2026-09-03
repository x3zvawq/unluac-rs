-- regress_463_generic_for_factory_root: iterator 工厂与 dispatch 函数有不同的根生命周期。
-- 工厂只用于初始化，但显式 local 的 VM 槽在循环体执行期间仍保活该工厂。
local builtin_ipairs = ipairs
local weak = setmetatable({}, { __mode = "v" })
ipairs = function(values)
    return builtin_ipairs(values)
end
weak.value = ipairs

local function run()
    local iterator = ipairs
    local values = { "one", "two" }
    local visits = 0
    for index, value in iterator(values) do
        ipairs = nil
        collectgarbage("collect")
        collectgarbage("collect")
        assert(weak.value ~= nil, "iterator factory was released inside loop body")
        assert(values[index] == value)
        visits = visits + 1
    end
    assert(visits == 2)
end

run()
collectgarbage("collect")
collectgarbage("collect")
assert(weak.value == nil, "iterator factory root outlived its frame")
ipairs = builtin_ipairs
print("regress_463_generic_for_factory_root", "OK")
