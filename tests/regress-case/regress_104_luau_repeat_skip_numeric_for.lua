-- regress_104_luau_repeat_skip_numeric_for#1: repeat 的条件 continue 可跳过完整 numeric-for
-- unluac: expect-contains [[repeat]]
-- unluac: expect-contains [[for ]]
-- unluac: expect-contains [[if not (]]
-- unluac: expect-not-contains [[else]]
-- unluac: expect-not-contains [[, nil, nil do]]
-- unluac: expect-not-contains [[goto ]]
-- unluac: expect-not-contains [[::L]]
-- unluac: expect-not-contains [[unresolved]]
-- unluac: expect-not-contains [[unluac error]]
local function run(a, b, xs)
    local x = 0
    for k, v in xs do
        repeat
            if a and b then
                continue
            end
            for i = 1, 3 do
                x = x + 1
            end
        until not b
    end
    return x
end

-- 部分布尔组合不会终止；只编译该 proto，避免执行阶段超时。
print("regress_104_luau_repeat_skip_numeric_for#1")
