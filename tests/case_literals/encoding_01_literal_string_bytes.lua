-- 三种独立字节边界：NUL 数字转义、开头换行、有效 UTF-8 控制字符。
-- 保留各自函数体与观察，不用共享 helper 改变常量和返回值布局。
-- unluac: expect-contains [["\255\000A"]]
-- unluac: expect-contains [["\nalpha"]]
-- unluac: expect-contains [["\194\133"]]
-- unluac: expect-ast-count [[function]] [[3]] [[@proto=0]]
-- unluac: expect-ast-max [[local-decl]] [[1]] [[@proto=1]]
-- unluac: expect-ast-max [[local-decl]] [[1]] [[@proto=2]]
-- unluac: expect-ast-max [[local-decl]] [[1]] [[@proto=3]]

local function run_binary()
    local value = "\255\000A"
    return #value, string.byte(value, 1), string.byte(value, 2), string.byte(value, 3)
end

local binary_length, binary_first, binary_second, binary_third = run_binary()
assert(binary_length == 3 and binary_first == 255 and binary_second == 0 and binary_third == 65)
print("regress_58_binary_string_bytes", binary_length, binary_first, binary_second, binary_third)

local function run_leading()
    local value = "\nalpha"
    return #value, string.byte(value, 1), string.sub(value, 2)
end

local leading_length, leading_first, leading_rest = run_leading()
assert(leading_length == 6 and leading_first == 10 and leading_rest == "alpha")
print("regress_55_leading_newline_string", leading_length, leading_first, leading_rest)

local function run_control()
    local value = "\194\133"
    return string.byte(value, 1), string.byte(value, 2), #value
end

local control_first, control_second, control_length = run_control()
assert(control_first == 194 and control_second == 133 and control_length == 2)
print("regress_57_utf8_control_string", control_first, control_second, control_length)
