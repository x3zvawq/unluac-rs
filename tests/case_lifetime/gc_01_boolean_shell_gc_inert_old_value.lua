-- 非相邻 primitive 旧值不承载 GC 资源，但不能因此删除原 truthiness 检查。
-- unluac: expect-contains [[not not]]
-- unluac: expect-ast-count [[generic-for]] [[1]]

for _, value in ipairs({ 1 }) do
    value = nil
    local marker = 7
    if value then
        value = true
    else
        value = false
    end
    assert(value == false)
    print("regress342-gc-inert-old-value", marker)
end
