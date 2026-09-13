-- 非 vararg NEWCLOSURE 的数值 capture 不能因常量传播变成共享 DUPCLOSURE。
-- unluac: expect-not-contains [[unresolved]]
-- unluac: expect-not-contains [[unluac error]]
local function opaque(value) return value end
local function integer_factory()
    local value = opaque(7)
    return function() return value end
end
local function positive_zero_factory()
    local value = opaque(0)
    return function() return value end
end
local function negative_zero_factory()
    local value = opaque(-0.0)
    return function() return value end
end
local function fraction_factory()
    local value = opaque(-0.1)
    return function() return value end
end
local function subnormal_factory()
    local value = opaque(5e-324)
    return function() return value end
end
local function largest_factory()
    local value = opaque(1.7976931348623157e308)
    return function() return value end
end

-- 间接读取阻止调用方内联 factory；capture 必须在不同 activation 中保持不同身份。
local cases = {
    { integer_factory, 7 },
    { positive_zero_factory, 0 },
    { negative_zero_factory, -0.0 },
    { fraction_factory, -0.1 },
    { subnormal_factory, 5e-324 },
    { largest_factory, 1.7976931348623157e308 },
}
for index, case in ipairs(cases) do
    local first = case[1]()
    local second = case[1]()
    assert(first ~= second, "fresh closures were shared")
    local actual = buffer.create(8)
    local expected = buffer.create(8)
    buffer.writef64(actual, 0, first())
    buffer.writef64(expected, 0, case[2])
    assert(buffer.tostring(actual) == buffer.tostring(expected), "capture bits changed")
    assert(first() == second())
    print("fresh-nonvararg", index, first == second, first() == second())
end
