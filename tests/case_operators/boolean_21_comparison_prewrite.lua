-- Boolean 值的原预写由完整调用帧消费；裸比较不能平白增加同样的预写。
-- unluac: expect-count [[and true]] [[3]] [[@dialect=luau]]
-- unluac: expect-contains [[assert(lhs == rhs)]] [[@debug=retained]]
-- unluac: expect-not-contains [[__eq = 0]]
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
        return true
    end,
}
local lhs, rhs = setmetatable({}, meta), setmetatable({}, meta)
direct(lhs, rhs)
prewritten(lhs, rhs)
message(lhs, rhs, "comparison must remain true")
assert(stringify(lhs, rhs) == "true")
assert(comparisons == 4)
print("boolean_21_comparison_prewrite", comparisons)
