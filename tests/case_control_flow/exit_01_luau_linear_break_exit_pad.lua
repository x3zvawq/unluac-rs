-- regress_107_luau_linear_break_exit_pad#1: O2 展开的独占线性块属于同一个 break exit pad
-- unluac: expect-contains [[for ]]
-- unluac: expect-contains [[repeat]]
-- unluac: expect-contains [[break]]
-- unluac: expect-contains [[until false]]
-- unluac: expect-not-contains [[goto ]]
-- unluac: expect-not-contains [[::L]]
-- unluac: expect-not-contains [[unresolved]]
-- unluac: expect-not-contains [[unluac error]]
local function run(a, xs)
    for k, v in xs do
        repeat
            if a then
                for i = 1, 3 do
                    print(k, v)
                    continue
                end
                break
            else
                for i = 1, 3 do
                    print(k, v)
                    print(k, v)
                end
            end
        until a
    end
end

-- 只用 -O2 验证结构恢复，不执行。
print("regress_107_luau_linear_break_exit_pad#1")
