-- pick=false 时读取仍先执行，比较已被编译器折叠为真值到 Boolean 的返回路径。
-- 同一闭包先用于 true 调用、再用于 false 写回；false/nil 保持自身，0/空串转换为 true。
-- 第二返回保留读取值及表身份，两次调用均只读取一次。
-- unluac: expect-ast-count [[function]] [[2]] [[@variant=O2]]
-- unluac: expect-ast-count [[numeric-for]] [[2]] [[@variant=O2]]
-- unluac: expect-ast-count [[if]] [[3]] [[@variant=O2]]
-- unluac: expect-ast-max [[local-binding]] [[14]] [[@variant=O2]]
-- unluac: expect-contains [[result, item = external(flag, 8, read, false)]] [[@variant=O2]] [[@debug=retained]]
-- unluac: expect-not-contains [[unluac error]]
local function external(enabled, value, read, pick)
    local item = read()
    return enabled and value == (pick and item or 8), item
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
        local expected_item = choices[selected]
        local expected = 8
        if selected == 1 or selected >= 3 then
            expected = expected_item
        end
        local expected_result = flag
        if enabled == 1 or enabled >= 3 then
            expected_result = true
        end
        local result, item = external(flag, expected, read, true)
        assert(result == expected_result and calls == 1)
        assert(rawequal(item, expected_item))
        calls = 0
        result, item = external(flag, 8, read, false)
        assert(result == expected_result and calls == 1)
        assert(rawequal(item, expected_item))
        print("external", enabled, selected, type(item), calls)
    end
end
