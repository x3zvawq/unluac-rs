-- Source parameter identity survives rebinding, captures, phi edges and shadow scopes.
-- 局部遮蔽结束后，闭包读取与比较应保持同一个调用参数表达式。
-- unluac: expect-not-contains [[= assert]]
-- unluac: expect-count [[() == ]] [[3]]
-- unluac: expect-ast-max [[local-binding]] [[8]]
-- unluac: expect-contains [[assert(read() == value)]] [[@debug=retained]]
local function update(value, count)
    assert(value == 5)
    for i = 1, count do value = value + i end
    local read = function() return value end
    value = value + 10
    do
        local value = 90
        value = value + 1
        assert(value == 91)
    end
    assert(read() == value)
    return value
end
assert(update(5, 3) == 21)
assert(update(5, 0) == 15)

local function branch(value, flag)
    if flag then value = 2 else value = 3 end
    value = value + 1
    return value
end
assert(branch(1, true) == 3)
assert(branch(1, false) == 4)

local function early(value)
    assert(type(value) == "table")
    local prior = function() return value end
    value = nil
    local read = function() return value end
    assert(prior() == nil)
    assert(read() == nil)
end
early({})
print("debug-param-identity", "OK")
