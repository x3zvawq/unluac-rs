-- unluac: expect-not-contains [[ // ]]
-- unluac: expect-not-contains [[ % ]]
-- unluac: expect-not-contains [[ & ]]
-- unluac: expect-not-contains [[ | ]]
-- unluac: expect-not-contains [[ ~ ]]
-- unluac: expect-not-contains [[ << ]]
-- unluac: expect-not-contains [[ >> ]]
-- unluac: expect-not-contains [[~17]]

local function discard_integer_ops()
    -- PUC does not constant-fold the comparison branch. inline-exprs first reduces each
    -- single-use result to 17, so the next cleanup round receives a literal operation tree.
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
