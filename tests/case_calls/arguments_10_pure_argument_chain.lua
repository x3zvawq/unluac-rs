-- FASTCALL direct 参数和普通调用共用依赖链，但保留各自的站点与参数复杂度约束。
-- 共用函数体保留逐次 NOT；O2 展开后的总量在字节码中核对，不靠源码复制操作。
-- unluac: expect-count [[not ]] [[31]]
-- unluac: expect-instruction-count [[not]] [[127]] [[@variant=O2]]
-- unluac: expect-ast-count [[assign]] [[17]] [[@proto=1]] [[@variant=O2]]
-- unluac: expect-ast-count [[assign]] [[8]] [[@proto=2]] [[@variant=O2]]
-- unluac: expect-contains [[--!optimize 2]] [[@variant=O2]]
-- 无读的原 Boolean 预写仍保留其值，不能在收尾时换成 nil 初始化。
-- unluac: expect-not-contains [[ = nil]]
-- unluac: expect-not-contains [[= assert]]
-- unluac: expect-not-contains [[= print]]
local function text(value)
    local result = not value
    result = not result; result = not result; result = not result; result = not result
    result = not result; result = not result; result = not result; result = not result
    result = not result; result = not result; result = not result; result = not result
    result = not result; result = not result; result = not result; result = not result
    result = not result
    return tostring(not not result)
end
assert(text(nil) == "false")
assert(text(false) == "false")
assert(text(0) == "true")
assert(text("") == "true")
local function kind(value)
    local result = not value
    result = not result; result = not result; result = not result; result = not result
    result = not result; result = not result; result = not result; result = not result
    return type(not not result)
end
assert(kind(0) == "boolean" and kind(nil) == "boolean")
print("regress_551_pure_argument_chain", "OK")
