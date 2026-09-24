-- 相邻 nil 初始化可以合并为一条 LOADNIL，声明与关闭边界仍分别属于三层作用域。
-- unluac: expect-not-contains [[unluac error]]
-- unluac: expect-ast-count [[do-block]] [[2]] [[@proto=0]]
-- unluac: expect-ast-max [[local-binding]] [[8]] [[@proto=0]]
-- unluac: expect-ast-count [[local-binding]] [[8]] [[@proto=0]] [[@debug=retained]]
-- Luau 的原字节码将 reused 的两个常量直接用于调用，不留下 stripped local。
-- unluac: expect-ast-count [[local-binding]] [[6]] [[@proto=0]] [[@dialect=luau]] [[@debug=stripped]]
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
    local reused = 17
    assert(write(reused) == 17)
end
local reused = 23
local outer, inner = read()
assert(outer == 17 and inner == 17)
assert(write(reused) == 17)
assert(read() == 23)
print("shared-nil-group", read(), reused)
