-- 连续嵌套调用复用前一条断言的结果槽；按当前 SSA 值版本恢复，不把旧读写混入新帧。
-- observed 的返回 COPY 仍属于比较参数，不能先提交为独立低槽赋值而截断完整调用。
-- unluac: expect-ast-count [[function]] [[5]] [[@variant=O2]]
-- unluac: expect-ast-count [[numeric-for]] [[4]] [[@variant=O2]]
-- unluac: expect-ast-count [[if]] [[0]] [[@variant=O2]]
-- unluac: expect-ast-max [[local-binding]] [[13]] [[@variant=O2]]
-- unluac: expect-contains [[assert(nested(enabled == 1, value, a == 1, b == 1) == expected)]] [[@variant=O2]] [[@debug=retained]]
-- unluac: expect-contains [[assert(observed(enabled == 1, value, read) == expected)]] [[@variant=O2]] [[@debug=retained]]
-- unluac: expect-contains [[local result = shared(enabled == 1, value, function(key)]] [[@variant=O2]] [[@debug=retained]]
-- unluac: expect-not-contains [[unluac error]]
local function nested(enabled, value, a, b)
    return enabled and value == ((a and 1 or 2) == (b and 1 or 2) and 7 or 8)
end

local function observed(enabled, value, read)
    return enabled and value == ((read("a") and 1 or 2) == (read("b") and 1 or 2) and 7 or 8)
end

local function shared(enabled, value, read)
    local item = read("shared")
    return enabled and value == (item and 7 or 8) and item == value
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
                assert(nested(enabled == 1, value, a == 1, b == 1) == expected)
                assert(observed(enabled == 1, value, read) == expected)
                assert(trace == (enabled == 1 and "ab" or ""))
                local calls = 0
                local result = shared(enabled == 1, value, function(key)
                    assert(key == "shared")
                    calls = calls + 1
                    return 7
                end)
                assert(result == (enabled == 1 and value == 7) and calls == 1)
                print("nested-value-operands", enabled, a, b, value, expected, trace, result, calls)
            end
        end
    end
end

