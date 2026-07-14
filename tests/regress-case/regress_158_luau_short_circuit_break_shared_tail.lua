-- regress_158_luau_short_circuit_break_shared_tail#1: 短路一臂经 guard break，另一臂直达共享 tail
-- unluac: expect-contains [[repeat]]
-- unluac: expect-not-contains [[goto ]]
-- unluac: expect-not-contains [[::L]]
-- unluac: expect-not-contains [[unresolved]]
-- unluac: expect-not-contains [[unluac error]]
local function run(a, b, c, xs)
    local x = 0
    repeat
        if not a then
            repeat
                if not (a or not a and (not c and a or c)) then
                    break
                end
                print(x)
                if xs[x] then
                    break
                end
                if a and b then
                    x += 1
                end
                for _ in xs, nil, nil do
                    x += 1
                    x += 1
                end
                if xs[x] then
                    break
                end
                print(x)
            until xs[x]
        end
    until a or c
    return x
end

print("regress_158_luau_short_circuit_break_shared_tail#1", run(true, true, false, {}))
