-- regress_07_close_scope_slot_reuse#1: close 后复用寄存器不能写回已关闭 upvalue
-- unluac: expect-ast-min [[function]] [[2]]
-- unluac: expect-not-contains [[(function()]]
-- unluac: expect-ast-count [[local-binding]] [[6]]
-- unluac: expect-ast-count [[do-block]] [[2]]
-- 两个独立捕获作用域仍写回同一外层绑定，不另建空的接棒声明。
-- unluac: expect-ast-count [[empty-local]] [[0]]
local u
do
    local count = 0
    local function co()
        count = count + 1
        return count
    end
    u = co
end

local first, second = u(), u()
assert(first == 1 and second == 2)
print("regress_07_close_scope_slot_reuse#1", first, second)

-- regress_07_close_scope_slot_reuse#2: 当前赋值 RHS 捕获同槽位时应写回原 local
local outer = 1
assert(u() == 3)
do
    local inner = 2
    inner = function()
        return inner
    end
    u = inner
end

assert(u() == u)
print("regress_07_close_scope_slot_reuse#2", outer)
assert(outer == 1)
