-- regress_200_close_managed_writable_capture#1: close-managed capture 在当前 epoch 内仍须保持可写身份
-- unluac: expect-not-contains [[unluac error]]
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
end

print("regress_200_close_managed_writable_capture#1", "OK")
