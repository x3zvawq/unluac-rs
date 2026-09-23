-- 每一臂仍含原字节码的 a 检查，不能因绑定稳定而提取公共条件。
-- p1_0 出现于一个参数声明和十八个检查；检查数量不依赖排版。
-- unluac: expect-count [[p1_0]] [[19]]
-- unluac: expect-ast-count [[if]] [[0]] [[@proto=1]]

local function choose(a, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18)
    return a and b1
        or a and b2
        or a and b3
        or a and b4
        or a and b5
        or a and b6
        or a and b7
        or a and b8
        or a and b9
        or a and b10
        or a and b11
        or a and b12
        or a and b13
        or a and b14
        or a and b15
        or a and b16
        or a and b17
        or a and b18
end

local rejected = choose(false, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18)
local selected = choose(true, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, 18)
assert(rejected == false)
assert(selected == 18)
print("regress_425_decision_naturalize_unbounded", rejected, selected)

-- 每个出口都实际命中，保持首个 truthy 值及 nil/false 的原返回语义。
local unpack_values = table.unpack or unpack
for selected_index = 1, 18 do
    local values = {}
    for index = 1, 18 do
        values[index] = index >= selected_index and index or false
    end
    assert(choose(true, unpack_values(values, 1, 18)) == selected_index)
end
assert(choose(nil, 1, 2, 3) == nil)
assert(choose(true, false, false, false) == nil)
