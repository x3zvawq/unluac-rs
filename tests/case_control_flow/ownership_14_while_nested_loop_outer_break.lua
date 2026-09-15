-- regress_281_while_nested_loop_outer_break: outer natural-loop exit进入nested loop后再break外层
-- unluac: expect-not-contains [[goto ]]
-- unluac: expect-not-contains [[::L]]
-- unluac: expect-not-contains [[unresolved]]
-- unluac: expect-not-contains [[unluac error]]
-- unluac: expect-ast-min [[while]] [[2]] [[@proto=1]]
-- unluac: expect-ast-min [[break]] [[1]] [[@proto=1]]
local function run(a, b, c)
    while a do
        if c then
            while b do
                print(1)
            end
            break
        end
    end
end

local entered = run(true, false, true)
local skipped = run(false, false, false)
assert(entered == nil and skipped == nil)
print("regress_281_while_nested_loop_outer_break", entered)
print("regress_281_while_nested_loop_outer_break", skipped)
