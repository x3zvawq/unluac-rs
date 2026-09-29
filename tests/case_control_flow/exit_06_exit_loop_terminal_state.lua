-- regress_94_multi_exit_loop_terminal_state#1: a terminal shared by body and post-loop keeps loop state
-- unluac: expect-not-contains [[goto ]]
-- unluac: expect-not-contains [[::L]]
-- unluac: expect-not-contains [[unresolved]]
-- unluac: expect-not-contains [[unluac error]]
-- 两次原检查都要保留，即使其中一支和下一句共享 break/return。
-- unluac: expect-ast-count [[if]] [[2]] [[@proto=1]]
-- unluac: expect-ast-count [[local-decl]] [[1]] [[@proto=1]]
-- unluac: expect-ast-count [[empty-local]] [[0]] [[@proto=1]]
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
-- false,false 的原循环不终止；补齐其余有限组合及 Lua 的真假值边界。
assert(run(true, true) == 0)
assert(run(0, false) == 0)
assert(run(nil, true) == 1)
print("regress_94_multi_exit_loop_terminal_state#1a", break_result)
print("regress_94_multi_exit_loop_terminal_state#1b", condition_result)
