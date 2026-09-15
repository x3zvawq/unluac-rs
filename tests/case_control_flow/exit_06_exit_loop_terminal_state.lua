-- regress_94_multi_exit_loop_terminal_state#1: a terminal shared by body and post-loop keeps loop state
-- unluac: expect-not-contains [[goto ]]
-- unluac: expect-not-contains [[::L]]
-- unluac: expect-not-contains [[unresolved]]
-- unluac: expect-not-contains [[unluac error]]
local function run(a, b)
    local x = 0
    repeat
        if a then
            if b then
                break
            end
            break
        end
        x = x + 1
    until b
    return x
end

local break_result = run(true, false)
local condition_result = run(false, true)
assert(break_result == 0 and condition_result == 1)
print("regress_94_multi_exit_loop_terminal_state#1a", break_result)
print("regress_94_multi_exit_loop_terminal_state#1b", condition_result)
