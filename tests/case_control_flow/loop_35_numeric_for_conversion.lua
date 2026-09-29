-- 三个输入必须按源码顺序求值；FORPREP 的成功后态不能提前应用到 header CALL。
-- unluac: expect-ast-min [[numeric-for]] [[1]]
-- unluac: expect-ast-count [[numeric-for]] [[4]]
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

local reverse_total = 0
for i = calls[1]("j", "3"), calls[1]("k", "1"), calls[1]("l", "-1") do
    assert(type(i) == "number")
    reverse_total = reverse_total + i
end
assert(reverse_total == 6 and trace == "abcdefghijkl")
print("numeric-conversion", total, trace, ok)
-- 完整 header 保留三个 CALL 的原求值顺序，不为初值、上界或步长留下准备变量。
-- unluac: expect-ast-count [[local-binding]] [[10]] [[@proto=0]]
-- unluac: expect-ast-count [[numeric-for]] [[3]] [[@proto=0]]
-- 所有 CALL 和状态写均保留；JIT 子 proto 按序列化顺序反排。
-- unluac: expect-ast-count [[call]] [[24]]
-- unluac: expect-ast-count [[call]] [[20]] [[@proto=0]]
-- unluac: expect-ast-count [[assign]] [[4]]
-- unluac: expect-ast-count [[local-binding]] [[0]] [[@proto=1]] [[@dialect=lua5.1]]
-- unluac: expect-ast-count [[local-binding]] [[1]] [[@proto=2]] [[@dialect=lua5.1]]
-- unluac: expect-ast-count [[numeric-for]] [[1]] [[@proto=2]] [[@dialect=lua5.1]]
-- unluac: expect-ast-count [[local-binding]] [[0]] [[@proto=1]] [[@dialect=lua5.2]]
-- unluac: expect-ast-count [[local-binding]] [[1]] [[@proto=2]] [[@dialect=lua5.2]]
-- unluac: expect-ast-count [[numeric-for]] [[1]] [[@proto=2]] [[@dialect=lua5.2]]
-- unluac: expect-ast-count [[local-binding]] [[0]] [[@proto=1]] [[@dialect=lua5.3]]
-- unluac: expect-ast-count [[local-binding]] [[1]] [[@proto=2]] [[@dialect=lua5.3]]
-- unluac: expect-ast-count [[numeric-for]] [[1]] [[@proto=2]] [[@dialect=lua5.3]]
-- unluac: expect-ast-count [[local-binding]] [[0]] [[@proto=1]] [[@dialect=lua5.4]]
-- unluac: expect-ast-count [[local-binding]] [[1]] [[@proto=2]] [[@dialect=lua5.4]]
-- unluac: expect-ast-count [[numeric-for]] [[1]] [[@proto=2]] [[@dialect=lua5.4]]
-- unluac: expect-ast-count [[local-binding]] [[0]] [[@proto=1]] [[@dialect=lua5.5]]
-- unluac: expect-ast-count [[local-binding]] [[1]] [[@proto=2]] [[@dialect=lua5.5]]
-- unluac: expect-ast-count [[numeric-for]] [[1]] [[@proto=2]] [[@dialect=lua5.5]]
-- unluac: expect-ast-count [[local-binding]] [[0]] [[@proto=2]] [[@dialect=luajit]]
-- unluac: expect-ast-count [[local-binding]] [[1]] [[@proto=1]] [[@dialect=luajit]]
-- unluac: expect-ast-count [[numeric-for]] [[1]] [[@proto=1]] [[@dialect=luajit]]
-- unluac: expect-ast-count [[local-binding]] [[0]] [[@proto=1]] [[@dialect=luau]]
-- unluac: expect-ast-count [[local-binding]] [[1]] [[@proto=2]] [[@dialect=luau]]
-- unluac: expect-ast-count [[numeric-for]] [[1]] [[@proto=2]] [[@dialect=luau]]
