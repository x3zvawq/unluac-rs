-- regress_109_luau_repeat_condition_entry_state#1: 短路条件入口保留局部 tail 的 loop state owner
-- unluac: expect-contains [[for ]]
-- unluac: expect-contains [[repeat]]
-- unluac: expect-contains [[until]]
-- unluac: expect-not-contains [[goto ]]
-- unluac: expect-not-contains [[::L]]
-- unluac: expect-not-contains [[unresolved]]
-- unluac: expect-not-contains [[unluac error]]
local function run(a, b, c, xs)
    local x = 0
    for k, v in xs do
        repeat
            if a then
                if xs[x] then
                    break
                end
            else
                repeat
                    x = x + 1
                    x = x + 1
                    break
                until not b
            end
            if a and b then
                print(x)
            end
            if xs[x] then
                break
            end
        until a or c
    end
    return x
end

-- 只验证结构恢复，不执行。
print("regress_109_luau_repeat_condition_entry_state#1")
