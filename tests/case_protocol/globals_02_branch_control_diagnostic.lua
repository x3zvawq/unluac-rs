-- 恒定未选 arm 不执行 ERRNNIL，但字节码仍有 TEST 和受其控制的 global initializer；
-- 不能据常量或外层 flag 删除原检查、未选 arm 和尾部声明。
-- unluac: expect-contains [[global unreachable_export]]
-- unluac: expect-ast-count [[if]] [[1]] [[@proto=1]]
-- unluac: expect-contains [[global tail_export]]
-- unluac: expect-ast-count [[function]] [[2]]
-- unluac: expect-ast-count [[if]] [[3]]
-- unluac: expect-ast-max [[local-binding]] [[4]]

local function unreachable_arm()
    if false then
        global unreachable_export = 71
        global<const> assert
        assert(unreachable_export == 71)
    end
    return 73
end

local function nested_unreachable_arm(flag)
    if flag then
        if flag then
            return 79
        end
        global tail_export = 83
        global<const> assert
        assert(tail_export == 83)
    end
    return 89
end

local direct = unreachable_arm()
local nested = nested_unreachable_arm(true)
assert(direct == 73 and nested == 79)
assert(nested_unreachable_arm(false) == 89)
assert(_ENV.unreachable_export == nil and _ENV.tail_export == nil)
print(
    "regress339-diagnostic",
    direct,
    nested
)
