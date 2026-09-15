-- regress_346_param_alias_generic_iterator_callback: generic-for 的隐式 iterator 调用必须参与参数 alias flow。
-- unluac: expect-not-contains [[local r2_0 = p2_0]]
-- unluac: expect-contains [[p2_0 = p2_0 + r2_0]]
-- unluac: expect-not-contains [[unluac error]]
local function iterator(limit, current)
    current = current + 1
    if current <= limit then
        return current
    end
end

local function run(value)
    for item in iterator, 2, 0 do
        value = value + item
    end
    return value
end

local value = run(10)
assert(value == 13)
print("regress_346_param_alias_generic_iterator_callback", value)
