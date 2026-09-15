-- regress_98_short_circuit_shared_return_value#1: explicit shared return value and prefix must survive a terminal truthy arm
-- unluac: expect-contains [[shared-tail-marker]]
-- unluac: expect-order [[shared-tail-marker]] [[return ]]
-- unluac: expect-not-contains [[goto ]]
-- unluac: expect-not-contains [[::L]]
-- unluac: expect-not-contains [[unresolved]]
-- unluac: expect-not-contains [[unluac error]]
-- Loop identity is allocated after HIR binding recovery; the contract is the numeric-for shape.
-- unluac: expect-contains [[for ]]
-- unluac: expect-contains [[ = 1, 3 do]]
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

local false_left = run(false, true)
local true_both = run(true, true)
local false_right = run(true, false)
assert(false_left == 0 and true_both == 3 and false_right == 0)
print("regress_98_short_circuit_shared_return_value#1", false_left)
print("regress_98_short_circuit_shared_return_value#2", true_both)
print("regress_98_short_circuit_shared_return_value#3", false_right)
