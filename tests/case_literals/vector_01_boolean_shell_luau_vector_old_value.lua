-- Luau vector constants are owned by the proto rather than the overwritten stack slot.
-- unluac: expect-not-contains [[not not]]
-- unluac: expect-not-contains [[if ]]

for _, value in ipairs({ 1 }) do
    value = vector.create(1.5, -2, 3.25)
    local marker = 7
    if value then
        value = true
    else
        value = false
    end
    print("regress342-luau-vector-old-value", marker)
end
