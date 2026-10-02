-- nil guard 不执行读取体；原第二实参 COPY 仍须随完整调用重发。
-- 分别观察单返回数量、实际 nil 值及两次调用后的计数，覆盖参数中的对象值。
-- 两个同形读取闭包要求 retained debug 恢复各自身份，stripped 不猜测已擦除的实参。
-- unluac: expect-ast-count [[function]] [[3]] [[@variant=O2]]
-- unluac: expect-ast-count [[numeric-for]] [[2]] [[@variant=O2]]
-- unluac: expect-ast-count [[if]] [[4]] [[@variant=O2]]
-- unluac: expect-ast-max [[local-binding]] [[11]] [[@variant=O2]]
-- unluac: expect-count [[valued(nil, expected, read)]] [[1]] [[@variant=O2]] [[@debug=retained]]
-- unluac: expect-count [[valued(nil, expected, other)]] [[1]] [[@variant=O2]] [[@debug=retained]]
-- unluac: expect-not-contains [[unluac error]]
local function valued(enabled, value, read)
    return enabled and value == (read() or 8)
end
local enabled_values = { [0] = false, true, [3] = 0, [4] = "" }
local choices = { [0] = false, 7, [3] = 0, [4] = "", [5] = {} }
for enabled = 0, 4 do
    local flag = enabled_values[enabled]
    for selected = 0, 5 do
        local calls = 0
        local function read()
            calls = calls + 1
            if selected == 1 then
                return 7
            end
            return choices[selected]
        end
        local function other()
            calls = calls + 1
            if selected == 1 then
                return 7
            end
            return choices[selected]
        end
        local expected = 8
        if selected == 1 or selected >= 3 then
            expected = choices[selected]
        end
        local expected_result = flag
        if enabled == 1 or enabled >= 3 then
            expected_result = true
        end
        assert(select("#", valued(nil, expected, read)) == 1 and calls == 0)
        print("valued", enabled, selected, calls, expected_result, valued(nil, expected, other))
        assert(calls == 0)
    end
end
