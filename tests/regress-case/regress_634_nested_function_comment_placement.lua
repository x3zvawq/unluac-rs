-- 单个父子函数树避免不同 VM 的兄弟 proto 排序差异，直接约束注释归属。
-- unluac: expect-contains [[nested = function() -- proto#1 params=]]
-- unluac: expect-order [[-- proto#1 params=]] [[-- proto#2 params=]]
local holder = {
    nested = function()
        local function child(value)
            return value + 2
        end
        return child
    end,
}
assert(holder.nested()(8) == 10)
print("nested-function-comments", holder.nested()(40))
