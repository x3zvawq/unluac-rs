global<const> assert, print, type
-- 只有权限声明的循环体可规约；合同保护读写权限和执行结果，不固定五个语法循环。
global shared_value = 1
local function run()
    repeat
        local body_function = function()
            global<const> shared_value
            repeat
                do
                    global *
                end
            until type(shared_value) == "number"
            return shared_value
        end
        assert(body_function() == 1)
    until (function()
        repeat
            global<const> shared_value
        until type(shared_value) == "number"
        return true
    end)()
    shared_value = 2
end
run()
assert(shared_value == 2)
global repeat_peer = 3
repeat
    do global<const> * end
until shared_value == 2
repeat
    do global<const> * end
until repeat_peer == 3
shared_value = 4
repeat_peer = 5
assert(shared_value + repeat_peer == 9)
print("repeat-permission-checkpoints", "OK")
