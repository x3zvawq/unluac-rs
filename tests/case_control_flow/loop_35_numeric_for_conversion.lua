-- 三个输入必须按源码顺序求值；FORPREP 的成功后态不能提前应用到 header CALL。
-- unluac: expect-ast-min [[numeric-for]] [[1]]
-- unluac: expect-ast-count [[numeric-for]] [[3]]
local trace = ""
local function control(label, value)
    trace = trace .. label
    return value
end
local calls = { control }
local total = 0
for i = calls[1]("a", "1"), calls[1]("b", "3"), calls[1]("c", "1") do
    assert(type(i) == "number")
    total = total + i
end
assert(total == 6 and trace == "abc")

for i = calls[1]("d", "3"), calls[1]("e", "1"), calls[1]("f", "1") do
    error("empty numeric loop entered")
end
assert(trace == "abcdef")

local entered_invalid_body = false
local ok = pcall(function()
    for i = calls[1]("g", "1"), calls[1]("h", "3"), calls[1]("i", "invalid") do
        entered_invalid_body = true
        error("invalid step entered body")
    end
end)
assert(not ok and not entered_invalid_body and trace == "abcdefghi")

print("numeric-conversion", total, trace, ok)
