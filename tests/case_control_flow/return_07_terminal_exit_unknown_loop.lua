-- regress_195_terminal_exit_unknown_loop#1: 多个 terminal exit 不应让无限循环退回 label/goto
-- unluac: expect-contains [[while ]]
-- unluac: expect-not-contains [[goto ]]
-- unluac: expect-not-contains [[::L]]
-- unluac: expect-not-contains [[unluac error]]
-- unluac: expect-ast-count [[while]] [[1]]
-- unluac: expect-ast-count [[local-binding]] [[12]] [[@dialect=lua5.1]]
-- unluac: expect-ast-count [[local-binding]] [[12]] [[@dialect=lua5.2]]
-- unluac: expect-ast-count [[local-binding]] [[12]] [[@dialect=lua5.3]]
-- unluac: expect-ast-count [[local-binding]] [[12]] [[@dialect=lua5.4]]
-- unluac: expect-ast-count [[local-binding]] [[12]] [[@dialect=lua5.5]]
-- unluac: expect-ast-count [[local-binding]] [[12]] [[@dialect=luajit]]
-- Luau 已将未修改的捕获常量放进闭包，不为它补回源码声明。
-- unluac: expect-ast-count [[local-binding]] [[11]] [[@dialect=luau]]
local saved
local token = {}

local function run(mode, actual_token)
    -- 同一 proto 同时暴露 branch-value call sink；不得因此对整个 proto 再跑
    -- 无边界的 temp-inline，把下面每轮更新的 first 常量化进循环条件。
    assert(actual_token == token)
    local first = 1
    while true do
        if mode == 3 and not first then
            return "done"
        end
        local value = "value"
        saved = function()
            return value
        end
        if mode == 1 then
            break
        elseif mode == 2 then
            return "return"
        elseif mode ~= 3 then
            error("bad mode")
        end
        first = nil
    end
end

local break_result = run(1, token)
local break_saved = saved()
local return_result = run(2, token)
local return_saved = saved()
local retry_result = run(3, token)
local retry_saved = saved()
local error_ok = pcall(run, 4, token)
assert(break_result == nil and break_saved == "value")
assert(return_result == "return" and return_saved == "value")
assert(retry_result == "done" and retry_saved == "value" and error_ok == false)
assert(saved() == "value")
assert(select("#", run(1, token)) == 0)
saved = nil
assert(not pcall(run, 1, {}))
assert(saved == nil)
assert(not pcall(run, nil, token))
assert(saved() == "value")

print(
    "regress_195_terminal_exit_unknown_loop#1",
    break_result,
    break_saved,
    return_result,
    return_saved,
    retry_result,
    retry_saved,
    error_ok
)
