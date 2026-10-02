-- 动态共享返回直接参与比较；原输入 Phi 连接调用结果，当前值版本与后继槽复用分离。
-- unluac: expect-ast-count [[function]] [[2]] [[@variant=O2]]
-- unluac: expect-ast-count [[numeric-for]] [[2]] [[@variant=O2]]
-- unluac: expect-ast-count [[if]] [[3]] [[@variant=O2]]
-- unluac: expect-ast-max [[local-binding]] [[11]] [[@variant=O2]]
-- unluac: expect-count [[shared(flag, expected, read)]] [[2]] [[@variant=O2]] [[@debug=retained]]
-- unluac: expect-contains [[assert(shared(flag, expected, read) == expected_shared and calls == 2)]] [[@variant=O2]] [[@debug=retained]]
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
        local expected_shared = flag
        if enabled == 1 or enabled >= 3 then
            expected_shared = selected == 1
        end
        assert(select("#", shared(flag, expected, read)) == 1 and calls == 1)
        assert(shared(flag, expected, read) == expected_shared and calls == 2)
        print("shared-flag", enabled, selected, calls, expected_shared)
    end
end
