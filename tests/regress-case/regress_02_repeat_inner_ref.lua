-- regress_02_repeat_inner_ref#1: until 条件引用循环体内声明的局部变量 (Lua 特有语义)
-- unluac: expect-contains [[local r1_2 = r1_1 * 2]]
-- unluac: expect-contains [[local r1_3 = r1_1 * 3]]
-- unluac: expect-contains [[until r1_2 > 10 or r1_3 > 20]]
-- unluac: expect-not-contains [[(function()]]
local function test_until_inner_ref()
    local result = {}
    local i = 0
    repeat
        i = i + 1
        local a = i * 2
        local b = i * 3
        result[i] = a + b
    until a > 10 or b > 20
    print("regress_02_repeat_inner_ref#1", i, result[i])
end

test_until_inner_ref()
