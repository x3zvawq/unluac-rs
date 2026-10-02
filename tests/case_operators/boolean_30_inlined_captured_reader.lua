-- 读闭包仅在 enabled 为真时执行；false、nil、0、空串和表值分别经过原短路路径。
-- O2 的两层展开仍应恢复完整调用，参数准备和捕获更新不留下机械中转。
-- unluac: expect-ast-count [[function]] [[2]] [[@variant=O2]]
-- unluac: expect-ast-count [[numeric-for]] [[2]] [[@variant=O2]]
-- unluac: expect-ast-count [[if]] [[4]] [[@variant=O2]]
-- unluac: expect-ast-max [[local-binding]] [[10]] [[@variant=O2]]
-- unluac: expect-contains [[assert(valued(flag, expected, read) == expected_result)]] [[@variant=O2]] [[@debug=retained]]
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
        local expected = 8
        if selected == 1 or selected >= 3 then
            expected = choices[selected]
        end
        local expected_result = flag
        if enabled == 1 or enabled >= 3 then
            expected_result = true
        end
        assert(valued(flag, expected, read) == expected_result)
        if enabled == 0 or enabled == 2 then
            assert(calls == 0)
        else
            assert(calls == 1)
        end
        print("valued", enabled, selected, calls)
    end
end
