-- 原比较、短路路径和整数运算均在字节码中，结果已知也不能删掉。
-- unluac: expect-contains [[ // ]]
-- unluac: expect-contains [[ % ]]
-- unluac: expect-contains [[ & ]]
-- unluac: expect-contains [[ | ]]
-- unluac: expect-contains [[ ~ ]]
-- unluac: expect-contains [[ << ]]
-- unluac: expect-contains [[ >> ]]
-- unluac: expect-contains [[~(]]
-- unluac: expect-count [[1 < 2 and 17 or 17]] [[8]]
-- unluac: expect-contains [[if 1 == 1 then]]
-- 原同槽更新即使没有后续读取，也不能绕过操作保留合同换成 nil。
-- unluac: expect-min-count [[ & ]] [[2]]
-- unluac: expect-min-count [[~]] [[3]]
-- unluac: expect-not-contains [[ = nil]]

local function discard_integer_ops()
    -- PUC 保留比较分支；值域可证明结果为 17，不代表这些操作属于恢复产生的包装。
    local unused_floor = ((1 < 2) and 17 or 17) // 3
    local unused_mod = ((1 < 2) and 17 or 17) % 3
    local unused_and = ((1 < 2) and 17 or 17) & 3
    local unused_or = ((1 < 2) and 17 or 17) | 3
    local unused_xor = ((1 < 2) and 17 or 17) ~ 3
    local unused_shl = ((1 < 2) and 17 or 17) << 3
    local unused_shr = ((1 < 2) and 17 or 17) >> 3
    local unused_not = ~((1 < 2) and 17 or 17)
    if 1 == 1 then
        print("discard-integer-ops")
    else
        print(
            unused_floor,
            unused_mod,
            unused_and,
            unused_or,
            unused_xor,
            unused_shl,
            unused_shr,
            unused_not
        )
    end
end

discard_integer_ops()

local function discard_binary_update()
    local value = 17
    value = value & 3
    print("discard-binary-update")
end

local function discard_unary_update()
    local value = 17
    value = ~value
    print("discard-unary-update")
end

discard_binary_update()
discard_unary_update()
