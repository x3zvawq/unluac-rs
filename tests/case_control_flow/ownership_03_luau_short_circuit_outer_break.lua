-- regress_113_luau_short_circuit_outer_break#1: 短路真臂跨内层 for 后退出外层 for
-- unluac: expect-contains [[ or ]]
-- unluac: expect-contains [[break]]
-- unluac: expect-not-contains [[goto ]]
-- unluac: expect-not-contains [[::L]]
-- unluac: expect-not-contains [[unresolved]]
-- unluac: expect-not-contains [[unluac error]]
local function run(a, b, c, xs)
    local x = 0
    for _, _ in xs do
        if a or c then
            for i = 1, 3 do
                print(x)
                print(x)
                print(x)
            end
            break
        else
            if a and b then
                x = x + 1
            end
        end
    end
    print(x)
    return x
end

print("regress_113_luau_nested_exit#1", run(false, false, true, { 1, 2 }))
