-- Luau 的具名声明先创建闭包，普通赋值先求目标；语法恢复须保留各自的求值顺序。
-- unluac: expect-contains [[.nested.declared()]]
-- unluac: expect-ast-count [[local-function]] [[2]] [[@proto=0]]
-- 普通赋值不能改成 Luau 的闭包优先声明，否则会把分配移到 __index 之前。
-- unluac: expect-contains [[.nested.assigned = function(]] [[@dialect=luau]]
local function declare(target, value)
    function target.nested.declared()
        return value
    end
end
local function assign(target, value)
    target.nested.assigned = function()
        return value
    end
end

local reads = 0
local leaf = {}
local target = setmetatable({}, {
    __index = function(_, key)
        assert(key == "nested")
        reads = reads + 1
        return leaf
    end,
})
declare(target, 17)
assert(reads == 1 and leaf.declared() == 17)
assign(target, 23)
assert(reads == 2 and leaf.assigned() == 23)
assert(leaf.declared() == 17)
print("flow_04_function_target_order", reads)
