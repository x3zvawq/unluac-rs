-- unluac: expect-contains [[-0x8000000000000000]]
-- unluac: expect-not-contains [[end)(]]
-- 原 value 是多值 RETURN 前的低槽前缀；检查整数发射及运行类型，不要求删除该声明。
-- unluac: expect-contains [[math.type(]]
-- unluac: expect-not-contains [[local r1_1 = r1_0]]
local function run()
    local value = -0x8000000000000000
    return value, math.type(value)
end

local state = 1
local function mutate()
    state = 2
    return 0
end

local function preserve_snapshot()
    local snapshot = state
    return mutate(), snapshot
end

local _, snapshot = preserve_snapshot()
assert(snapshot == 1)
print("regress_59_integer_min_literal", run())
