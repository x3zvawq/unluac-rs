-- Boolean 值的原预写由完整调用帧消费；裸比较不能平白增加同样的预写。
-- unluac: expect-count [[and true]] [[3]] [[@dialect=luau]]
-- unluac: expect-contains [[assert(lhs == rhs)]] [[@debug=retained]]
-- unluac: expect-not-contains [[__eq = 0]]
-- unluac: expect-ast-count [[function]] [[5]]
-- unluac: expect-ast-count [[if]] [[0]]
-- unluac: expect-ast-max [[local-binding]] [[11]]
-- 并列 RHS 共享 Luau scratch，不能拆出 CALL 结果和参数 COPY 的声明链。
-- unluac: expect-ast-count [[local-decl]] [[3]] [[@proto=0]] [[@dialect=luau]]
-- PUC/LuaJIT 编译器保留三个 marker 比较，stripped 的常量内联不能删除这些操作。
-- unluac: expect-count [[ == 1]] [[3]] [[@dialect=lua5.1]]
-- unluac: expect-count [[ == 1]] [[3]] [[@dialect=lua5.2]]
-- unluac: expect-count [[ == 1]] [[3]] [[@dialect=lua5.3]]
-- unluac: expect-count [[ == 1]] [[3]] [[@dialect=lua5.4]]
-- unluac: expect-count [[ == 1]] [[3]] [[@dialect=lua5.5]]
-- unluac: expect-count [[ == 1]] [[3]] [[@dialect=luajit]]
local function direct(lhs, rhs)
    assert(lhs == rhs)
end
local function prewritten(lhs, rhs)
    local marker = 1
    assert(lhs == rhs and marker == 1)
end
local function message(lhs, rhs, text)
    local marker = 1
    assert(lhs == rhs and marker == 1, text)
end
local function stringify(lhs, rhs)
    local marker = 1
    return tostring(lhs == rhs and marker == 1)
end
local comparisons = 0
local meta = {
    __eq = function()
        comparisons = comparisons + 1
        return comparisons <= 4
    end,
}
local lhs, rhs = setmetatable({}, meta), setmetatable({}, meta)
direct(lhs, rhs)
prewritten(lhs, rhs)
message(lhs, rhs, "comparison must remain true")
assert(stringify(lhs, rhs) == "true")
assert(comparisons == 4)
print("boolean_21_comparison_prewrite", comparisons)
-- 同一对操作数的后续比较改为 false，必须走失败路径并保留 assert 消息。
assert(not pcall(direct, lhs, rhs))
assert(comparisons == 5)
assert(not pcall(prewritten, lhs, rhs))
assert(comparisons == 6)
assert(string.find(select(2, pcall(message, lhs, rhs, "comparison sentinel")), "comparison sentinel", 1, true))
assert(comparisons == 7)
assert(stringify(lhs, rhs) == "false")
assert(comparisons == 8)
-- 原生值相等不调用 __eq；三个无 return 的包装函数均返回零个值。
assert(select("#", direct(7, 7)) == 0)
assert(select("#", prewritten(false, false)) == 0)
assert(select("#", message("same", "same", "same value")) == 0)
assert(stringify(7, 7) == "true" and comparisons == 8)
