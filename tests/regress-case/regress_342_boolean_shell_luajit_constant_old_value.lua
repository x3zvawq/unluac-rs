-- LuaJIT KCDATA constants are owned by the proto rather than the overwritten stack slot.
-- unluac: expect-not-contains [[not not]]
-- unluac: expect-not-contains [[if ]]

for _, value in ipairs({ 1 }) do
    value = 1LL
    local marker = 7
    if value then
        value = true
    else
        value = false
    end
    print("regress342-luajit-int64-old-value", marker)
end

for _, value in ipairs({ 1 }) do
    value = 1ULL
    local marker = 8
    if value then
        value = true
    else
        value = false
    end
    print("regress342-luajit-uint64-old-value", marker)
end

for _, value in ipairs({ 1 }) do
    value = 1i
    local marker = 9
    if value then
        value = true
    else
        value = false
    end
    print("regress342-luajit-complex-old-value", marker)
end
