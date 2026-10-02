-- 匿名读取实参先创建闭包，再检查标签并更新捕获计数；false guard 也必须读取一次。
-- 参数、共享 item 和结果预写应恢复为完整调用，不留下外置闭包或断言中转。
-- unluac: expect-ast-count [[function]] [[2]] [[@variant=O2]]
-- unluac: expect-ast-count [[numeric-for]] [[4]] [[@variant=O2]]
-- unluac: expect-ast-count [[if]] [[0]] [[@variant=O2]]
-- unluac: expect-ast-max [[local-binding]] [[8]] [[@variant=O2]]
-- unluac: expect-contains [[local result = shared(enabled == 1, value, function(key)]] [[@variant=O2]] [[@debug=retained]]
-- unluac: expect-not-contains [[unluac error]]
local function shared(enabled, value, read)
    local item = read("shared")
    return enabled and value == (item and 7 or 8) and item == value
end
for enabled = 0, 1 do
    for a = 0, 1 do
        for b = 0, 1 do
            for value = 7, 8 do
                local calls = 0
                local result = shared(enabled == 1, value, function(key)
                    assert(key == "shared")
                    calls = calls + 1
                    return 7
                end)
                assert(result == (enabled == 1 and value == 7) and calls == 1)
                print("anonymous-shared", enabled, a, b, value, result, calls)
            end
        end
    end
end
