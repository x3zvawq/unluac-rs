-- 显式 GBK 解码覆盖恰好也能作为 UTF-8 的短字节；生成层转码不改变 IR 字节身份。
-- unluac: expect-contains [[中文]]
-- unluac: expect-contains [[一]]
-- unluac: expect-not-contains [[\214\208]]
local function text()
    return "\214\208\206\196", "\210\187"
end
local a, b = text()
assert(a == "\214\208\206\196" and b == "\210\187")
local labels = { ["\214\208\206\196"] = 7, ["\210\187"] = 9 }
assert(labels[a] == 7 and labels[b] == 9)
local quoted = "\214\208\"'\\\0009"
assert(quoted == a:sub(1, #a / 2) .. "\"'\\\0009")
local multiline = "\214\208\n\206\196"
assert(multiline == a:sub(1, #a / 2) .. "\n" .. a:sub(#a / 2 + 1))
print("readable-gbk-ok", labels[a], labels[b])
