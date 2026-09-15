-- 相同读取的内层返回合并后不应留下无声明 block，阻止外层继续消费共同来源。
-- unluac: expect-contains [[return p1_0.value]]
-- unluac: expect-not-contains [[if p1_]]
-- 同槽、无观察的提前返回可整体表达式化；falsy 叶不能套用 and/or 选择。
-- unluac: expect-ast-count [[if]] [[0]] [[@proto=3]]
-- unluac: expect-ast-min [[if]] [[1]] [[@proto=4]]
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

local function early_literal(flag)
    if flag then return "selected" end
    return "fallback"
end

local function early_falsy(flag, nullish)
    if flag then
        if nullish then return nil end
        return false
    end
    return "fallback"
end

assert(early_literal(false) == "fallback" and early_literal(nil) == "fallback")
assert(early_literal(true) == "selected" and early_literal(0) == "selected")
assert(early_literal("") == "selected" and early_literal({}) == "selected")
assert(early_falsy(false, true) == "fallback")
assert(early_falsy(true, false) == false)
assert(early_falsy(true, true) == nil)
assert(select("#", early_falsy(true, true)) == 1)
