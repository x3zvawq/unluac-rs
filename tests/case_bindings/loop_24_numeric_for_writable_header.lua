-- 可写 index 另占源码槽；Luau 三个 header CALL 均在完整预留区之后返回。
-- unluac: expect-ast-min [[numeric-for]] [[1]]
-- unluac: expect-ast-count [[numeric-for]] [[1]]
-- Lua 5.5 的 index 是 const，本样例按现有可写 numeric-for 方言矩阵注册。
local trace = ""
local function control(label, value)
    trace = trace .. label
    return value
end
local calls = { control }
local total = 0
for i = calls[1]("j", "1"), calls[1]("k", "3"), calls[1]("l", "1") do
    i = i + 10
    total = total + i
end
assert(total == 36 and trace == "jkl")
print("writable-numeric-header", total, trace)
