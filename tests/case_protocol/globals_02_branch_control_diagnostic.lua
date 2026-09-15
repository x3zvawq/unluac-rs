-- Lua 5.5 global 声明只在执行到 initializer 时运行 ERRNNIL；恒定未选 arm 不会执行，
-- 且声明的词法效力不越过该 arm，因此不应留下不可达分支外壳。
-- unluac: expect-not-contains [[global unreachable_export]]
-- unluac: expect-not-contains [[global tail_export]]

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
print(
    "regress339-diagnostic",
    direct,
    nested
)
