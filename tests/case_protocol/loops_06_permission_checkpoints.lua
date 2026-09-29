-- unluac: expect-ast-count [[repeat]] [[1]] [[@proto=1]]
-- unluac: expect-count [[type(shared_value)]] [[2]]
-- unluac: expect-ast-count [[call]] [[1]] [[@proto=2]]
-- unluac: expect-ast-count [[call]] [[1]] [[@proto=3]]
-- unluac: expect-ast-count [[function]] [[3]]
-- unluac: expect-ast-max [[local-binding]] [[4]]
-- unluac: expect-ast-count [[assign]] [[5]]
-- unluac: expect-ast-count [[do-block]] [[0]] [[@proto=0]]
global<const> assert, print, type
-- 空正文可用直接 while 表达；权限声明可整理，原条件的读取与判断仍须保留。
global shared_value = 1
local body_calls, condition_calls = 0, 0
local function run()
    repeat
        local body_function = function()
            body_calls = body_calls + 1
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
        condition_calls = condition_calls + 1
        repeat
            global<const> shared_value
        until type(shared_value) == "number"
        return true
    end)()
    shared_value = 2
end
run()
assert(shared_value == 2)
assert(body_calls == 1 and condition_calls == 1)
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
