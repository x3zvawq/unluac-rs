-- regress_358_temp_inline_repeated_closure: loop condition 的嵌套 call 参数不能重复分配 closure
-- unluac: expect-contains [[while condition and consume(]]
-- unluac: expect-not-contains [[consume(function()]]
-- unluac: expect-not-contains [[unluac error]]

state = { count = 0 }

function consume(callback)
    state.count = state.count + 1
    if state.first == nil then
        state.first = callback
    end
    assert(state.first == callback)
    return state.count < 2
end

condition = true
local callback = function() end
while condition and consume(callback) do
end

assert(state.count == 2)
print("loop-closure-region", state.count)
