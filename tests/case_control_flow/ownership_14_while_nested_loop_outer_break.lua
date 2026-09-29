-- regress_281_while_nested_loop_outer_break: outer natural-loop exit进入nested loop后再break外层
-- unluac: expect-not-contains [[goto ]]
-- unluac: expect-not-contains [[::L]]
-- unluac: expect-not-contains [[unresolved]]
-- unluac: expect-not-contains [[unluac error]]
-- unluac: expect-ast-count [[while]] [[2]]
-- unluac: expect-ast-count [[break]] [[1]]
-- unluac: expect-ast-count [[if]] [[1]]
-- unluac: expect-ast-count [[local-binding]] [[5]]
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
assert(run(0, false, "") == nil)
assert(run("", nil, 0) == nil)
assert(run(nil, true, true) == nil)
local saved_print = print
local visits = 0
-- 内层真条件不终止；打印观察主动中断，证明执行的是内层回边。
print = function(value)
    assert(value == 1)
    visits = visits + 1
    assert(visits < 3, "observed inner loop backedge")
end
assert(not pcall(run, true, true, true))
assert(visits == 3)
visits = 0
assert(not pcall(run, "", 0, ""))
assert(visits == 3)
print = saved_print
print("regress_281_while_nested_loop_outer_break", entered)
print("regress_281_while_nested_loop_outer_break", skipped)
