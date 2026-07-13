-- regress_111_luau_short_continue_shared_tail#1: 短路 continue 与 break 共享本轮 for tail
-- unluac: expect-contains [[for ]]
-- unluac: expect-contains [[repeat]]
-- unluac: expect-contains [[continue]]
-- unluac: expect-contains [[break]]
-- unluac: expect-not-contains [[goto ]]
-- unluac: expect-not-contains [[::L]]
-- unluac: expect-not-contains [[unresolved]]
-- unluac: expect-not-contains [[unluac error]]
local function run(a, b, c, xs)
    local x = 0
    for k, v in xs do
        if a then
            for i = 1, 3 do
                x = x + 1
                repeat
                    x = x + 1
                until b
            end
        else
            if a or c then
                if a and b then
                    x = x + 1
                end
            else
                x = x + 1
                continue
            end
            if a and b then
                print(x)
                if xs[x] then
                    break
                end
            end
        end
        x = x + 1
    end
    return x
end

print("regress_111_luau_short_continue_shared_tail#1", run(false, true, false, {}))
