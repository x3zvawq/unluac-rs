-- Lua 5.5 global 声明的 ERRNNIL 是显式诊断，不能随常量未选 arm 静默删除。
-- unluac: expect-contains [[global unreachable_export]]
-- unluac: expect-contains [[global tail_export]]

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

print(
    "regress339-diagnostic",
    unreachable_arm(),
    nested_unreachable_arm(true)
)
