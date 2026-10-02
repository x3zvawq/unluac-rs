-- 先读取捕获状态，再返回比较结果和同一读取值；false/nil 的 enabled 也必须读取一次。
-- 读取值覆盖 false、nil、数字、空串和表，双返回值保持身份且不留下展开中转。
-- unluac: expect-ast-count [[function]] [[2]] [[@variant=O2]]
-- unluac: expect-ast-count [[numeric-for]] [[2]] [[@variant=O2]]
-- unluac: expect-ast-count [[if]] [[3]] [[@variant=O2]]
-- unluac: expect-ast-max [[local-binding]] [[14]] [[@variant=O2]]
-- unluac: expect-contains [[local result, item = external(flag, expected, read, true)]] [[@variant=O2]] [[@debug=retained]]
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
        print("external", enabled, selected, type(item), calls)
    end
end
