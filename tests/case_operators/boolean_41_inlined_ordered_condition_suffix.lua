-- 展开调用之间的有序比较仍重发原数值准备槽，条件帧参与整批前缀验证。
-- unluac: expect-ast-count [[function]] [[2]] [[@variant=O2]]
-- unluac: expect-ast-count [[numeric-for]] [[5]] [[@variant=O2]]
-- unluac: expect-ast-count [[if]] [[4]] [[@variant=O2]]
-- unluac: expect-ast-max [[local-binding]] [[14]] [[@variant=O2]]
-- unluac: expect-count [[shared(flag, expected, read)]] [[2]] [[@variant=O2]] [[@debug=retained]]
-- unluac: expect-contains [[if enabled <= 1 and selected <= 1 then]] [[@variant=O2]] [[@debug=retained]]
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
        assert(select("#", shared(flag, expected, read)) == 1 and calls == 1)
        if enabled <= 1 and selected <= 1 then
            print("ordered-suffix", enabled, selected, calls)
        end
        local expected_shared = flag
        if enabled == 1 or enabled >= 3 then
            expected_shared = selected == 1
        end
        assert(shared(flag, expected, read) == expected_shared and calls == 2)
        print("shared-flag", enabled, selected, calls, expected_shared)
    end
end

-- 后续独立循环复用 read 的物理槽；不能使前一初始化的只读参数视图失效。
for later_a = 0, 2 do
    for later_b = 0, 2 do
        for later_c = 0, 40 do
            print("later-register-reuse", later_a, later_b, later_c)
        end
    end
end
