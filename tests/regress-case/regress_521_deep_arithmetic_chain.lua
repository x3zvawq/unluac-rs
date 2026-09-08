-- 长左结合运算链应通过完整管线；不能靠重新结合或截断绕过递归深度。
local function sum(a)
    return
        a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a +
        a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a +
        a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a +
        a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a +
        a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a +
        a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a +
        a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a +
        a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a +
        a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a +
        a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a +
        a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a +
        a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a +
        a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a +
        a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a +
        a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a +
        a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a +
        a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a +
        a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a +
        a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a +
        a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a +
        a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a +
        a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a +
        a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a +
        a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a +
        a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a +
        a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a +
        a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a +
        a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a +
        a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a +
        a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a +
        a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a +
        a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a +
        a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a +
        a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a +
        a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a +
        a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a +
        a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a +
        a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a +
        a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a +
        a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a +
        a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a +
        a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a +
        a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a +
        a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a +
        a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a +
        a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a +
        a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a +
        a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a +
        a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a +
        a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a +
        a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a +
        a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a +
        a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a +
        a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a +
        a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a +
        a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a +
        a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a +
        a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a +
        a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a +
        a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a +
        a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a +
        a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a +
        a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a +
        a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a +
        a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a +
        a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a +
        a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a +
        a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a +
        a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a +
        a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a +
        a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a +
        a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a +
        a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a +
        a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a +
        a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a +
        a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a +
        a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a +
        a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a +
        a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a +
        a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a +
        a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a +
        a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a +
        a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a +
        a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a +
        a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a +
        a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a +
        a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a +
        a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a +
        a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a +
        a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a +
        a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a +
        a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a +
        a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a +
        a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a +
        a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a +
        a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a +
        a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a +
        a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a +
        a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a +
        a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a +
        a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a +
        a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a +
        a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a +
        a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a +
        a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a +
        a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a +
        a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a +
        a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a +
        a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a +
        a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a +
        a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a +
        a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a +
        a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a +
        a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a +
        a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a +
        a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a +
        a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a +
        a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a +
        a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a +
        a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a +
        a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a +
        a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a +
        a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a +
        a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a +
        a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a +
        a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a +
        a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a +
        a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a
end

print("number", sum(2))
print("fraction", string.format("%.17g", sum(0.1)))

-- 非结合元方法同时检查操作数顺序和调用次数。
local count = 0
local mt = {}
mt.__add = function(left, right)
    count = count + 1
    return setmetatable({ value = (left.value * 3 + right.value) % 65521 }, mt)
end
local value = setmetatable({ value = 2 }, mt)
local result = sum(value)
local expected = 2
for i = 1, 2047 do
    expected = (expected * 3 + 2) % 65521
end
assert(result.value == expected and count == 2047)
print("metamethod", result.value, count)
