-- regress_200_close_managed_writable_capture#1: close-managed capture 在当前 epoch 内仍须保持可写身份
-- unluac: expect-not-contains [[unluac error]]
-- unluac: expect-ast-count [[local-binding]] [[2]]
-- unluac: expect-ast-count [[do-block]] [[1]]
do
    local written
    local proxy = {}
    setmetatable(proxy, {
        __newindex = function(target, key, value)
            written = true
            rawset(target, key, value)
        end,
    })

    written = false
    proxy.value = 42
    assert(written)
    assert(proxy.value == 42)
    written = false
    proxy.value = 43
    assert(not written and proxy.value == 43)
    proxy.other = 99
    assert(written and proxy.other == 99)
end

print("regress_200_close_managed_writable_capture#1", "OK")
