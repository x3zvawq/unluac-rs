-- 嵌套构造器占用的槽随后由 nil 声明复用；恢复字段不能再额外引入空声明。
-- 原 nil 批次与后继分配共用四个源码绑定，构造器和调用不得留下接棒变量。
-- unluac: expect-ast-count [[local-binding]] [[4]] [[@proto=1]]
-- unluac: expect-ast-max [[assign]] [[3]] [[@proto=1]]
-- unluac: expect-ast-count [[table-constructor]] [[7]]

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
