-- regress_195_terminal_exit_unknown_loop#1: 多个 terminal exit 不应让无限循环退回 label/goto
-- unluac: expect-contains [[while ]]
-- unluac: expect-not-contains [[goto ]]
-- unluac: expect-not-contains [[::L]]
-- unluac: expect-not-contains [[unluac error]]
local saved

local function run(mode)
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

local break_result = run(1)
local break_saved = saved()
local return_result = run(2)
local return_saved = saved()
local retry_result = run(3)
local retry_saved = saved()
local error_ok = pcall(run, 4)

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
