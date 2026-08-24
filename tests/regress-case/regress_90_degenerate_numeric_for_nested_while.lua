-- regress_90_degenerate_numeric_for_nested_while#1: unreachable numeric latch may share nested while header
-- unluac: expect-contains [[for ]]
-- unluac: expect-contains [[while ]]
-- unluac: expect-not-contains [[while not true do]]
-- unluac: expect-contains [[while false do]]
-- unluac: expect-contains [[break]]
-- unluac: expect-not-contains [[goto ]]
-- unluac: expect-not-contains [[::L]]
-- unluac: expect-not-contains [[unresolved]]
-- unluac: expect-not-contains [[unluac error]]
local function run(a, b, xs)
    local x = 0
    if a and b then
        print(x)
        for _ = 1, 3 do
            while not b do
                if a then
                    continue
                end
                print(x)
                if xs[x] then
                    break
                end
            end
            break
        end
    end
    return x
end

print("regress_90_degenerate_numeric_for_nested_while#1", run(false, true, {}))
