-- regress_206_luau_home_slot_compaction#1: stripped 大函数应按 home slot 复用 local，避免源码局部槽膨胀
-- unluac: expect-not-contains [[unluac error]]
-- unluac: expect-not-contains [[do]]
local function churn(x)
    x = bit32.bxor(bit32.lrotate(x, 1), bit32.rrotate(x, 1)); x = bit32.bxor(bit32.lrotate(x, 2), bit32.rrotate(x, 8)); x = bit32.bxor(bit32.lrotate(x, 3), bit32.rrotate(x, 15)); x = bit32.bxor(bit32.lrotate(x, 4), bit32.rrotate(x, 22))
    x = bit32.bxor(bit32.lrotate(x, 5), bit32.rrotate(x, 29)); x = bit32.bxor(bit32.lrotate(x, 6), bit32.rrotate(x, 5)); x = bit32.bxor(bit32.lrotate(x, 7), bit32.rrotate(x, 12)); x = bit32.bxor(bit32.lrotate(x, 8), bit32.rrotate(x, 19))
    x = bit32.bxor(bit32.lrotate(x, 9), bit32.rrotate(x, 26)); x = bit32.bxor(bit32.lrotate(x, 10), bit32.rrotate(x, 2)); x = bit32.bxor(bit32.lrotate(x, 11), bit32.rrotate(x, 9)); x = bit32.bxor(bit32.lrotate(x, 12), bit32.rrotate(x, 16))
    x = bit32.bxor(bit32.lrotate(x, 13), bit32.rrotate(x, 23)); x = bit32.bxor(bit32.lrotate(x, 14), bit32.rrotate(x, 30)); x = bit32.bxor(bit32.lrotate(x, 15), bit32.rrotate(x, 6)); x = bit32.bxor(bit32.lrotate(x, 16), bit32.rrotate(x, 13))
    x = bit32.bxor(bit32.lrotate(x, 17), bit32.rrotate(x, 20)); x = bit32.bxor(bit32.lrotate(x, 18), bit32.rrotate(x, 27)); x = bit32.bxor(bit32.lrotate(x, 19), bit32.rrotate(x, 3)); x = bit32.bxor(bit32.lrotate(x, 20), bit32.rrotate(x, 10))
    x = bit32.bxor(bit32.lrotate(x, 21), bit32.rrotate(x, 17)); x = bit32.bxor(bit32.lrotate(x, 22), bit32.rrotate(x, 24)); x = bit32.bxor(bit32.lrotate(x, 23), bit32.rrotate(x, 31)); x = bit32.bxor(bit32.lrotate(x, 24), bit32.rrotate(x, 7))
    x = bit32.bxor(bit32.lrotate(x, 25), bit32.rrotate(x, 14)); x = bit32.bxor(bit32.lrotate(x, 26), bit32.rrotate(x, 21)); x = bit32.bxor(bit32.lrotate(x, 27), bit32.rrotate(x, 28)); x = bit32.bxor(bit32.lrotate(x, 28), bit32.rrotate(x, 4))
    x = bit32.bxor(bit32.lrotate(x, 29), bit32.rrotate(x, 11)); x = bit32.bxor(bit32.lrotate(x, 30), bit32.rrotate(x, 18)); x = bit32.bxor(bit32.lrotate(x, 31), bit32.rrotate(x, 25)); x = bit32.bxor(bit32.lrotate(x, 1), bit32.rrotate(x, 1))
    x = bit32.bxor(bit32.lrotate(x, 2), bit32.rrotate(x, 8)); x = bit32.bxor(bit32.lrotate(x, 3), bit32.rrotate(x, 15)); x = bit32.bxor(bit32.lrotate(x, 4), bit32.rrotate(x, 22)); x = bit32.bxor(bit32.lrotate(x, 5), bit32.rrotate(x, 29))
    x = bit32.bxor(bit32.lrotate(x, 6), bit32.rrotate(x, 5)); x = bit32.bxor(bit32.lrotate(x, 7), bit32.rrotate(x, 12)); x = bit32.bxor(bit32.lrotate(x, 8), bit32.rrotate(x, 19)); x = bit32.bxor(bit32.lrotate(x, 9), bit32.rrotate(x, 26))
    x = bit32.bxor(bit32.lrotate(x, 10), bit32.rrotate(x, 2)); x = bit32.bxor(bit32.lrotate(x, 11), bit32.rrotate(x, 9)); x = bit32.bxor(bit32.lrotate(x, 12), bit32.rrotate(x, 16)); x = bit32.bxor(bit32.lrotate(x, 13), bit32.rrotate(x, 23))
    x = bit32.bxor(bit32.lrotate(x, 14), bit32.rrotate(x, 30)); x = bit32.bxor(bit32.lrotate(x, 15), bit32.rrotate(x, 6)); x = bit32.bxor(bit32.lrotate(x, 16), bit32.rrotate(x, 13)); x = bit32.bxor(bit32.lrotate(x, 17), bit32.rrotate(x, 20))
    x = bit32.bxor(bit32.lrotate(x, 18), bit32.rrotate(x, 27)); x = bit32.bxor(bit32.lrotate(x, 19), bit32.rrotate(x, 3)); x = bit32.bxor(bit32.lrotate(x, 20), bit32.rrotate(x, 10)); x = bit32.bxor(bit32.lrotate(x, 21), bit32.rrotate(x, 17))
    x = bit32.bxor(bit32.lrotate(x, 22), bit32.rrotate(x, 24)); x = bit32.bxor(bit32.lrotate(x, 23), bit32.rrotate(x, 31)); x = bit32.bxor(bit32.lrotate(x, 24), bit32.rrotate(x, 7)); x = bit32.bxor(bit32.lrotate(x, 25), bit32.rrotate(x, 14))
    x = bit32.bxor(bit32.lrotate(x, 26), bit32.rrotate(x, 21)); x = bit32.bxor(bit32.lrotate(x, 27), bit32.rrotate(x, 28)); x = bit32.bxor(bit32.lrotate(x, 28), bit32.rrotate(x, 4)); x = bit32.bxor(bit32.lrotate(x, 29), bit32.rrotate(x, 11))
    x = bit32.bxor(bit32.lrotate(x, 30), bit32.rrotate(x, 18)); x = bit32.bxor(bit32.lrotate(x, 31), bit32.rrotate(x, 25)); x = bit32.bxor(bit32.lrotate(x, 1), bit32.rrotate(x, 1)); x = bit32.bxor(bit32.lrotate(x, 2), bit32.rrotate(x, 8))
    return x
end

print("regress_206_luau_home_slot_compaction#1", churn(12345))
