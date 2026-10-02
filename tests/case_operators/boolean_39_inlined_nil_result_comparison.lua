-- 内联后的 nil 返回是普通 Def；比较查询须保留其原输入身份，完整消费断言预写。
-- unluac: expect-ast-count [[function]] [[2]] [[@variant=O2]]
-- unluac: expect-ast-count [[numeric-for]] [[2]] [[@variant=O2]]
-- unluac: expect-ast-count [[if]] [[3]] [[@variant=O2]]
-- unluac: expect-ast-max [[local-binding]] [[11]] [[@variant=O2]]
-- unluac: expect-contains [[assert(shared(nil, expected, read) == nil and calls == 2)]] [[@variant=O2]] [[@debug=retained]]
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
        assert(shared(nil, expected, read) == nil and calls == 2)
        print("shared", enabled, selected, calls, expected_result, nil)
    end
end
