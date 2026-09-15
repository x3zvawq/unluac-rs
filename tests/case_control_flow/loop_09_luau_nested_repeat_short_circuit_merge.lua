-- regress_151_luau_nested_repeat_short_circuit_merge#1: 短路链尾与 plain if-then 共享本轮 merge
-- unluac: expect-contains [[repeat]]
-- unluac: expect-not-contains [[not (p1_0 or p1_2)]]
-- unluac: expect-not-contains [[goto ]]
-- unluac: expect-not-contains [[::L]]
-- unluac: expect-not-contains [[unresolved]]
-- unluac: expect-not-contains [[unluac error]]
local function run(a, b, c, xs)
    local x = 0
    repeat
        if not a then
            local done
            repeat
                if not (a or c) then
                    if not (a or c) then
                        break
                    end
                    print(x)
                    done = xs[x]
                    if done then
                        break
                    end
                end
                if a and b then
                    x += 1
                end
                for _ in xs do
                    x += 1
                    x += 1
                end
                if xs[x] then
                    break
                end
                print(x)
                done = xs[x]
            until done
        end
    until a or c
    return x
end

print("regress_151_luau_nested_repeat_short_circuit_merge#1", run(true, true, false, {}))
