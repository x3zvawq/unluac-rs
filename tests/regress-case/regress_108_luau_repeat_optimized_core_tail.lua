-- regress_108_luau_repeat_optimized_core_tail#1: O2 展开块沿当前 loop core 恢复 tail guard
-- unluac: expect-contains [[repeat]]
-- unluac: expect-contains [[if not]]
-- unluac: expect-not-contains [[goto ]]
-- unluac: expect-not-contains [[::L]]
-- unluac: expect-not-contains [[unresolved]]
-- unluac: expect-not-contains [[unluac error]]
local function optimized_tail(a, b)
    local x = 0
    repeat
        print(x)
        for i = 1, 3 do
            x = x + 1
            print(x)
            if a and b then
                break
            end
        end
    until a
    return x
end

-- 只验证结构恢复，不执行。
print("regress_108_luau_repeat_optimized_core_tail#1")
