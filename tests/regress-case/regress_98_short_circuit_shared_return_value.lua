-- regress_98_short_circuit_shared_return_value#1: explicit shared return value and prefix must survive a terminal truthy arm
-- unluac: expect-contains [[shared-tail-marker]]
-- unluac: expect-order [[shared-tail-marker]] [[return ]]
-- unluac: expect-not-contains [[goto ]]
-- unluac: expect-not-contains [[::L]]
-- unluac: expect-not-contains [[unresolved]]
-- unluac: expect-not-contains [[unluac error]]
-- unluac: expect-contains [[for r1_3 = 1, 3 do]]
local function run(a, b)
    local x = 0
    if a and b then
        print(x)
        for _ = 1, 3 do
            x = x + 1
        end
        if a and b then
            print(x)
            for _ = 1, 3 do
                break
            end
        end
    end
    print("shared-tail-marker")
    return x
end

print("regress_98_short_circuit_shared_return_value#1", run(false, true))
