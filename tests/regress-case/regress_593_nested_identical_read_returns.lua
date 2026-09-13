-- 相同读取的内层返回合并后不应留下无声明 block，阻止外层继续消费共同来源。
-- unluac: expect-contains [[return p1_0.value]]
-- unluac: expect-not-contains [[if p1_]]
local function read(t, a, b, c)
    if a then
        return t.value
    elseif b then
        return t.value
    elseif c then
        return t.value
    else
        return t.value
    end
end

local count = 0
local proxy = setmetatable({}, {__index = function(_, key)
    count = count + 1
    assert(key == "value")
    return count
end})
for mask = 0, 7 do
    local value = read(proxy, mask >= 4, mask % 4 >= 2, mask % 2 == 1)
    assert(value == mask + 1)
end
assert(count == 8)
print("identical-read-returns", count)
