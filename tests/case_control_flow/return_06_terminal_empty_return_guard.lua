-- regress_189_terminal_empty_return_guard#1: 空 return guard 不与尾 return 清理反复互换
-- unluac: expect-contains [[pcall]]
-- unluac: expect-not-contains [[unluac error]]
-- unluac: expect-ast-count [[if]] [[2]]
-- unluac: expect-ast-count [[local-binding]] [[4]]

local function run()
    if pcall(function()
        print("regress_189_terminal_empty_return_guard#1")
    end, nil) then
        return
    else
        return
    end
end

run()

local saved_print = print
local calls, should_fail = 0, false
print = function(message)
    assert(message == "regress_189_terminal_empty_return_guard#1")
    calls = calls + 1
    if should_fail then
        error("callback failure")
    end
end
assert(select("#", run()) == 0 and calls == 1)
should_fail = true
assert(select("#", run()) == 0 and calls == 2)
should_fail = nil
assert(select("#", run()) == 0 and calls == 3)
print = saved_print
