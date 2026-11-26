-- 相邻 nil 初始化可以合并为一条 LOADNIL，声明与关闭边界仍分别属于三层作用域。
-- Luau 的原字节码将 reused 的两个常量直接用于调用，不留下 stripped local。
local write, read
do
    local outer
    do
        local inner
        write = function(next_value)
            outer = next_value
            inner = inner or next_value
            return inner
        end
        read = function()
            return outer, inner
        end
    end
    assert(select("#", read()) == 2 and read() == nil and select(2, read()) == nil)
    local reused = 17
    assert(write(reused) == 17)
end
local reused = 23
local outer, inner = read()
assert(outer == 17 and inner == 17)
assert(write(reused) == 17)
assert(read() == 23)
print("shared-nil-group", read(), reused)
