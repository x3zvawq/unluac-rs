-- regress_281_while_nested_loop_outer_break: outer natural-loop exit进入nested loop后再break外层
-- unluac: expect-not-contains [[goto ]]
-- unluac: expect-not-contains [[::L]]
-- unluac: expect-not-contains [[unresolved]]
-- unluac: expect-not-contains [[unluac error]]
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

print("regress_281_while_nested_loop_outer_break", type(run))
