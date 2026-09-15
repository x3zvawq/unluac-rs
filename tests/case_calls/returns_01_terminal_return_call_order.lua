-- regress_173_terminal_return_call_order#1: 末尾调用不能越过前置 return value 提前执行
-- unluac: expect-not-contains [[unluac error]]
local function terminal_return_call()
    local state = 1
    local object = {}
    object.call = function()
        state = 2
        return 3
    end
    local callee = object.call
    return state, callee()
end

local state, result = terminal_return_call()
assert(state == 1 and result == 3)
print("regress_173_terminal_return_call_order#1", state, result)
