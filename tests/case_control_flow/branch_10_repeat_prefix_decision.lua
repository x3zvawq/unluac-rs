-- regress_370_repeat_prefix_decision: an untouched prefix Decision does not own the repeat tail
-- unluac: expect-contains [[until stop() or again()]]
-- unluac: expect-not-contains [[unresolved]]
-- unluac: expect-contains [[function stop()]]
-- unluac: expect-contains [[function again()]]
-- unluac: expect-not-contains [[global function]]
-- unluac: expect-ast-count [[local-binding]] [[2]]
-- unluac: expect-ast-count [[if]] [[2]]
-- unluac: expect-ast-count [[repeat]] [[1]]
-- unluac: expect-ast-count [[while]] [[1]]

stop_calls, again_calls = 0, 0
stop_result, again_result = true, false

function stop()
    stop_calls = stop_calls + 1
    return stop_result
end

function again()
    again_calls = again_calls + 1
    return again_result
end

local function run(a, b, c)
    repeat
        local x = 0
        if a then
            if c then
                x = x + 1
            end
            repeat
            until b
        end
        print(x)
        if stop() then
            break
        end
    until again()
end

run(true, true, true)
assert(stop_calls == 1 and again_calls == 0)

-- 尾部第二项必须仅在第一项为 false 时执行；前缀的两层条件也分别走过。
stop_result, again_result = false, true
run(true, true, false)
run(false, true, true)
assert(stop_calls == 3 and again_calls == 2)
stop_result = true
run(true, true, true)
assert(stop_calls == 4 and again_calls == 2)
