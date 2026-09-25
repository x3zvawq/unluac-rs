-- 嵌套构造器占用的槽随后由 nil 声明复用；恢复字段不能再额外引入空声明。
-- Luau 的逐槽 nil 写应直接承接四个绑定；PUC 的批次声明布局独立验证运行与收敛。
-- unluac: expect-ast-count [[local-binding]] [[4]] [[@proto=1]] [[@dialect=luau]]

local function run()
    local root = { items = { { value = 11 }, { value = 22 } } }
    local first, second, list
    first = { value = 33 }
    second = { value = 44 }
    list = { first, second }
    assert(root.items[1].value == 11 and root.items[2].value == 22)
    assert(list[1].value == 33 and list[2].value == 44)
    print(root.items[1].value, root.items[2].value, list[1].value, list[2].value)
end

run()
