-- 原调用先完成三个 Boolean 实参，再执行带嵌套选值的短路返回；低槽 value 直接复用。
-- unluac: expect-ast-count [[function]] [[1]]
-- unluac: expect-ast-count [[numeric-for]] [[4]]
-- unluac: expect-ast-count [[if]] [[0]]
-- PUC/JIT 可保留复杂返回的一个命名中间值；Luau 原完整帧无需参数和结果中转。
-- unluac: expect-ast-max [[local-binding]] [[7]]
-- unluac: expect-ast-max [[local-binding]] [[6]] [[@dialect=luau]]
-- unluac: expect-count [[and 1 or 2]] [[2]] [[@dialect=luau]]
local function nested(enabled, value, a, b)
    return enabled and value == ((a and 1 or 2) == (b and 1 or 2) and 7 or 8)
end
for enabled = 0, 1 do
    for a = 0, 1 do
        for b = 0, 1 do
            for value = 7, 8 do
                local expected = enabled == 1 and value == (a == b and 7 or 8)
                assert(nested(enabled == 1, value, a == 1, b == 1) == expected)
            end
        end
    end
end
print("inlined-value-expression", "OK")
