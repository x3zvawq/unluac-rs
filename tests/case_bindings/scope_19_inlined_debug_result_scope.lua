-- Luau 内联块返回的 debug 绑定必须先在外层声明；后一次赋值不能夺走首次初始化。
-- 观察器在编译边界外检查环境，避免 getfenv/setfenv 改变被测模块的内联决策。
-- unluac: expect-ast-count [[local-binding]] [[4]] [[@proto=1]]
-- 两个捕获块之外，第二组三结果在低槽写回后须退出临时声明域，恢复后继 assert 的原帧。
-- unluac: expect-ast-count [[do-block]] [[3]] [[@proto=0]] [[@variant=O2]]
-- unluac: expect-not-contains [[assert(r0_]] [[@variant=O2]] [[@debug=retained]]
-- unluac: expect-ast-count [[goto]] [[0]]
-- unluac: expect-ast-count [[label]] [[0]]
-- unluac-runtime: local run = ...
-- unluac-runtime: local env = setmetatable({}, { __index = getfenv() })
-- unluac-runtime: setfenv(run, env)
-- unluac-runtime: run()
-- unluac-runtime: assert(next(env) == nil, "unexpected global write: " .. tostring(next(env)))

local function capture_chain(flag, original)
    local alias = original
    local function replace()
        alias = false
    end
    replace()
    local chosen, marker
    if flag then
        marker = 1
        chosen = alias
    else
        marker = 2
        chosen = alias
    end
    return chosen, original, marker
end

local selected, original, marker = capture_chain(true, true)
assert(selected == false and original == true and marker == 1)
selected, original, marker = capture_chain(false, true)
assert(selected == false and original == true and marker == 2)
print("inlined_debug_result_scope")
