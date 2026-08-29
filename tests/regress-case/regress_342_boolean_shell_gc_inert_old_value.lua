-- regress_342_boolean_shell_gc_inert_old_value: 非相邻 primitive 旧值允许删除 dead boolean shell
-- unluac: expect-not-contains [[not not]]

for _, value in ipairs({ 1 }) do
    value = nil
    local marker = 7
    if value then
        value = true
    else
        value = false
    end
    print("regress342-gc-inert-old-value", marker)
end
