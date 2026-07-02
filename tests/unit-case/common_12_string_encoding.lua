-- common_12_string_encoding#1: auto编码识别非UTF-8字符串
-- unluac: expect-contains [["中文"]]
local function test_gbk_string_literal()
    local value = "\214\208\206\196"
    return value
end

test_gbk_string_literal()
