-- regress_106_luau_repeat_current_iteration_tail#1: early continue 不能跨迭代抢占共享 tail
-- unluac: expect-contains [[repeat]]
-- unluac: expect-contains [[while ]]
-- unluac: expect-contains [[for ]]
-- unluac: expect-contains [[break]]
-- unluac: expect-not-contains [[goto ]]
-- unluac: expect-not-contains [[::L]]
-- unluac: expect-not-contains [[unresolved]]
-- unluac: expect-not-contains [[unluac error]]
local function run(a, b, c, xs)
    local x = 0
    repeat
        if a then
            if xs[x] then
                continue
            end
            while b do
                x = x + 1
            end
            repeat
                if a or c then
                    print(x)
                else
                    break
                end
            until a and b
        else
            repeat
                for k, v in xs do
                    break
                end
            until b
            if xs[x] then
                print(x)
            end
        end
        if a and b then
            break
        end
    until a
    return x
end

-- 该 proto 可能不终止；只用 -O2 验证结构恢复，不执行。
print("regress_106_luau_repeat_current_iteration_tail#1")
