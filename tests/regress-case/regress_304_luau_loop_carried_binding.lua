-- regress_304_luau_loop_carried_binding: 同槽loop-carried状态直接复用源码binding
-- unluac: expect-contains [[        r1_0 = r1_0 + 1]]
-- unluac: expect-contains [[            r1_1 = r1_1 +]]
-- unluac: expect-not-contains [[        local r1_2 = r1_0 + 1]]
-- unluac: expect-not-contains [[        r1_0, r1_1 =]]
-- unluac: expect-not-contains [[local r1_3]]
local function run(enabled, choose_first, limit)
    local count, value = 0, 0
    while count < limit do
        count = count + 1
        if enabled then
            local step = choose_first and 1 or 2
            value = value + step
        end
    end
    return value, count
end

print("regress_304_luau_loop_carried_binding", run(true, false, 3), run(false, true, 4))
