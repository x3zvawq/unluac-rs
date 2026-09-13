-- 原高槽 CALL 的单结果经两次低槽 MOVE 写回；完整帧须保留赋值和后继 COPY，避免每轮新增 callee。
local function probe(argument)
    local first, second = "left", "right"
    local target = type
    local alias = target
    alias = alias(argument)
    target = alias
    return first, second, target
end
local a,b,c = probe({})
assert(a=="left" and b=="right" and c=="table")
print(a,b,c)
