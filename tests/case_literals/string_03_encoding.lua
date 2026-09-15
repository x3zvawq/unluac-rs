-- common_12_string_encoding#1: 解码展示不能改变非 UTF-8 字符串的原始字节。
-- unluac: expect-contains [["\214\208\206\196"]]
-- unluac: expect-count [["中文"]] [[1]]
-- unluac: expect-contains [[\214\208\n\206\196]]
local function test_gbk_string_literal()
    local value = "\214\208\206\196"
    return value
end

local value = test_gbk_string_literal()
assert(#value == 4)
assert(string.byte(value, 1) == 214 and string.byte(value, 2) == 208)
assert(string.byte(value, 3) == 206 and string.byte(value, 4) == 196)
print("common_12_string_encoding#1", #value, string.byte(value, 1, 4))

-- 真正的 UTF-8 仍应可读；非 UTF-8 的换行、引号和后接数字不能借长括号或转义改变值。
local strings = {
    "\228\184\173\230\150\135",
    "\214\208\n\206\196",
    "\214\208\"'7",
    "\000\2559",
}
local expected = {
    { 228, 184, 173, 230, 150, 135 },
    { 214, 208, 10, 206, 196 },
    { 214, 208, 34, 39, 55 },
    { 0, 255, 57 },
}
for i, text in ipairs(strings) do
    assert(#text == #expected[i])
    local bytes = {}
    for j = 1, #text do
        local byte = string.byte(text, j)
        assert(byte == expected[i][j])
        bytes[j] = byte
    end
    print("common_12_string_encoding#2", i, table.concat(bytes, ","))
end
