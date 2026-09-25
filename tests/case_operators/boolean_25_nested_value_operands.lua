-- 内部 phi 是比较的操作数；两侧取值、外层短路及多层嵌套分别保留控制与单次求值。
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

local function valued(enabled, value, read)
    return enabled and value == (read() or 8)
end

local function external(enabled, value, read, pick)
    local item = read()
    return enabled and value == (pick and item or 8), item
end

for enabled = 0, 1 do
    for selected = 0, 1 do
        local calls = 0
        local function read()
            calls = calls + 1
            if selected == 1 then
                return 7
            end
            return false
        end
        local expected = 8
        if selected == 1 then
            expected = 7
        end
        assert(valued(enabled == 1, expected, read) == (enabled == 1))
        assert(calls == enabled)
        calls = 0
        local result, item = external(enabled == 1, expected, read, true)
        assert(result == (enabled == 1) and calls == 1)
        assert(item == (selected == 1 and 7 or false))
        print("operand-once", enabled, selected, result, item, calls)
    end
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

-- unluac: expect-not-contains [[goto ]]
-- unluac: expect-ast-count [[if]] [[0]] [[@proto=1]]
-- unluac: expect-ast-count [[if]] [[0]] [[@proto=2]]
-- unluac: expect-ast-count [[call]] [[1]] [[@proto=4]]
-- unluac: expect-ast-count [[call]] [[1]] [[@proto=5]]
-- Luau 的原返回帧直接承接短路值，不应逐轮增加 flag 的局部转交。
-- unluac: expect-ast-count [[local-binding]] [[0]] [[@proto=1]] [[@dialect=luau]]
-- unluac: expect-ast-count [[local-binding]] [[0]] [[@proto=2]] [[@dialect=luau]]
-- unluac: expect-ast-count [[local-binding]] [[1]] [[@proto=3]] [[@dialect=luau]]
-- unluac: expect-ast-count [[local-binding]] [[0]] [[@proto=4]] [[@dialect=luau]]
