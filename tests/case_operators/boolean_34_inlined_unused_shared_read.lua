-- nil 仅折叠返回判断；急切读取仍须执行，且其未读取的两臂写入不可丢弃。
-- 同时覆盖并入 select 参数的 nil 和保留源码声明的 nil，观察返回数量及两次读取计数。
-- unluac: expect-ast-count [[function]] [[2]] [[@variant=O2]]
-- unluac: expect-ast-count [[numeric-for]] [[2]] [[@variant=O2]]
-- unluac: expect-ast-count [[if]] [[3]] [[@variant=O2]]
-- unluac: expect-ast-max [[local-binding]] [[12]] [[@variant=O2]]
-- unluac: expect-count [[shared(nil, expected, read)]] [[2]] [[@variant=O2]] [[@debug=retained]]
-- unluac: expect-contains [[local result = shared(nil, expected, read)]] [[@variant=O2]] [[@debug=retained]]
-- unluac: expect-not-contains [[unluac error]]
local function shared(enabled, value, read)
    local item = read("shared")
    return enabled and value == (item and 7 or 8) and item == value
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
        local expected = 8
        if selected == 1 or selected >= 3 then
            expected = choices[selected]
        end
        local expected_result = flag
        if enabled == 1 or enabled >= 3 then
            expected_result = true
        end
        assert(select("#", shared(nil, expected, read)) == 1 and calls == 1)
        local result = shared(nil, expected, read)
        print("shared", enabled, selected, calls, expected_result, result)
        assert(result == nil and calls == 2)
    end
end
