-- 外层 false guard 不读取；true guard 按 a、b 的顺序读取并追加 trace。
-- 原预写和嵌套选值属于完整调用，不应留下条件副本、空结果声明或断言中转。
-- unluac: expect-ast-count [[function]] [[2]] [[@variant=O2]]
-- unluac: expect-ast-count [[numeric-for]] [[4]] [[@variant=O2]]
-- unluac: expect-ast-count [[if]] [[0]] [[@variant=O2]]
-- unluac: expect-ast-max [[local-binding]] [[9]] [[@variant=O2]]
-- unluac: expect-contains [[local result = observed(enabled == 1, value, read)]] [[@variant=O2]] [[@debug=retained]]
-- unluac: expect-not-contains [[unluac error]]
local function observed(enabled, value, read)
    return enabled and value == ((read("a") and 1 or 2) == (read("b") and 1 or 2) and 7 or 8)
end
for enabled = 0, 1 do
    for a = 0, 1 do
        for b = 0, 1 do
            for value = 7, 8 do
                local trace = ""
                local function read(key)
                    trace = trace .. key
                    return key == "a" and a == 1 or key == "b" and b == 1
                end
                local expected = enabled == 1 and value == (a == b and 7 or 8)
                local result = observed(enabled == 1, value, read)
                assert(result == expected)
                assert(trace == (enabled == 1 and "ab" or ""))
                print("observed", enabled, a, b, value, expected, trace, result)
            end
        end
    end
end
