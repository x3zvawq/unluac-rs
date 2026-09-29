-- 内部 phi 是比较的操作数；两侧取值、外层短路及多层嵌套分别保留控制与单次求值。
-- unluac: expect-ast-count [[function]] [[9]]
-- unluac: expect-ast-count [[numeric-for]] [[8]]
-- 混合字段的嵌套表临时槽已在首个观察前覆盖；后续捕获不应拆开先前的初始化。
-- unluac: expect-contains [[{ [0] = false, 7, [3] = 0, [4] = "", [5] = {} }]] [[@dialect=luau]] [[@variant=O0]] [[@debug=stripped]]
-- 被消费的表临时根不应留下占位声明，后继数值控制写仍属于完整循环头。
-- unluac: expect-contains [[for r0_7 = 0, 4 do]] [[@dialect=luau]] [[@variant=O0]] [[@debug=stripped]]
-- unluac: expect-contains [[assert(r0_3(r0_8, r0_13, r0_11) == r0_14)]] [[@dialect=luau]] [[@variant=O0]] [[@debug=stripped]]
-- O1 的 step 复用原表临时槽；空声明与三个控制值须作为完整循环头一并恢复。
-- unluac: expect-contains [[for r0_7 = 0, 4 do]] [[@dialect=luau]] [[@variant=O1]] [[@debug=stripped]]
-- unluac: expect-contains [[assert(r0_3(r0_8, r0_13, r0_11) == r0_14)]] [[@dialect=luau]] [[@variant=O1]] [[@debug=stripped]]
-- debug 身份在末次字段写之后生效，混合数组批次及后继控制槽仍可整体恢复。
-- unluac: expect-contains [[local choices = { [0] = false, 7, [3] = 0, [4] = "", [5] = {} }]] [[@dialect=luau]] [[@debug=retained]]
-- unluac: expect-contains [[for enabled = 0, 4 do]] [[@dialect=luau]] [[@debug=retained]]
-- 短路末叶沿用原 epoch，后继调用帧与既有结果写回不能因其临时声明连带退化。
-- unluac: expect-contains [[result, item = external(flag, 8, read, false)]] [[@dialect=luau]] [[@variant=O1]] [[@debug=retained]]
-- unluac: expect-contains [[assert(result == expected_result and calls == 1 and rawequal(item, expected_item))]] [[@dialect=luau]] [[@variant=O1]] [[@debug=retained]]
-- expected_shared 的分支先于 shared 调用；保留独立边界后，外层断言仍是完整调用。
-- unluac: expect-contains [[assert(r0_2(r0_8, r0_13, r0_11) == r0_17 and r0_10 == 3)]] [[@dialect=luau]] [[@variant=O1]] [[@debug=stripped]]
-- 默认返回复杂度上限会保留 nested/observed 的两个长表达式声明；Luau 原返回帧无需此中转。
-- unluac: expect-ast-max [[local-binding]] [[35]]
-- unluac: expect-ast-max [[local-binding]] [[33]] [[@dialect=luau]]
-- 高槽 Boolean 结果写回已有低槽后，不应留下预写声明并使下一轮调用重新分裂。
-- unluac: expect-max-count [[ = assert]] [[0]] [[@dialect=luau]] [[@variant=O0]] [[@debug=stripped]]
-- 无写入的合流 pad 不应令后继调用逐轮退回准备别名。
-- unluac: expect-max-count [[ = assert]] [[0]] [[@dialect=lua5.1]]
-- unluac: expect-max-count [[ = assert]] [[0]] [[@dialect=lua5.2]]
-- unluac: expect-max-count [[ = assert]] [[0]] [[@dialect=lua5.3]]
-- unluac: expect-max-count [[ = assert]] [[0]] [[@dialect=lua5.4]]
-- unluac: expect-max-count [[ = assert]] [[0]] [[@dialect=lua5.5]]
-- 共享比较终端直接写回原目标；控制前缀不能复制终端或制造两个结果快照。
-- unluac: expect-ast-max [[local-binding]] [[31]] [[@proto=0]] [[@dialect=luajit]]
-- unluac: expect-count [[r0_17 = r0_9 == 1]] [[1]] [[@dialect=luajit]] [[@debug=stripped]]
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
        assert(valued(flag, expected, read) == expected_result)
        if enabled == 0 or enabled == 2 then
            assert(calls == 0)
        else
            assert(calls == 1)
        end
        calls = 0
        local result, item = external(flag, expected, read, true)
        assert(result == expected_result and calls == 1)
        assert(rawequal(item, expected_item))
        if enabled <= 1 and selected <= 1 then
            print("operand-once", enabled, selected, result, item, calls)
        end
        calls = 0
        result, item = external(flag, 8, read, false)
        assert(result == expected_result and calls == 1 and rawequal(item, expected_item))
        calls = 0
        assert(select("#", external(flag, 8, read, false)) == 2 and calls == 1)
        assert(select("#", valued(nil, expected, read)) == 1 and calls == 1)
        assert(shared(nil, expected, read) == nil and calls == 2)
        local expected_shared = flag
        if enabled == 1 or enabled >= 3 then
            expected_shared = selected == 1
        end
        assert(shared(flag, expected, read) == expected_shared and calls == 3)
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
-- unluac: expect-ast-count [[if]] [[0]] [[@proto=1]] [[@dialect=lua5.1]]
-- unluac: expect-ast-count [[if]] [[0]] [[@proto=1]] [[@dialect=lua5.2]]
-- unluac: expect-ast-count [[if]] [[0]] [[@proto=1]] [[@dialect=lua5.3]]
-- unluac: expect-ast-count [[if]] [[0]] [[@proto=1]] [[@dialect=lua5.4]]
-- unluac: expect-ast-count [[if]] [[0]] [[@proto=1]] [[@dialect=lua5.5]]
-- unluac: expect-ast-count [[if]] [[0]] [[@proto=1]] [[@dialect=luau]]
-- unluac: expect-ast-count [[if]] [[0]] [[@proto=9]] [[@dialect=luajit]]
-- unluac: expect-ast-count [[if]] [[0]] [[@proto=2]] [[@dialect=lua5.1]]
-- unluac: expect-ast-count [[if]] [[0]] [[@proto=2]] [[@dialect=lua5.2]]
-- unluac: expect-ast-count [[if]] [[0]] [[@proto=2]] [[@dialect=lua5.3]]
-- unluac: expect-ast-count [[if]] [[0]] [[@proto=2]] [[@dialect=lua5.4]]
-- unluac: expect-ast-count [[if]] [[0]] [[@proto=2]] [[@dialect=lua5.5]]
-- unluac: expect-ast-count [[if]] [[0]] [[@proto=2]] [[@dialect=luau]]
-- unluac: expect-ast-count [[if]] [[0]] [[@proto=8]] [[@dialect=luajit]]
-- unluac: expect-ast-count [[call]] [[1]] [[@proto=4]] [[@dialect=lua5.1]]
-- unluac: expect-ast-count [[call]] [[1]] [[@proto=4]] [[@dialect=lua5.2]]
-- unluac: expect-ast-count [[call]] [[1]] [[@proto=4]] [[@dialect=lua5.3]]
-- unluac: expect-ast-count [[call]] [[1]] [[@proto=4]] [[@dialect=lua5.4]]
-- unluac: expect-ast-count [[call]] [[1]] [[@proto=4]] [[@dialect=lua5.5]]
-- unluac: expect-ast-count [[call]] [[1]] [[@proto=4]] [[@dialect=luau]]
-- unluac: expect-ast-count [[call]] [[1]] [[@proto=6]] [[@dialect=luajit]]
-- unluac: expect-ast-count [[call]] [[1]] [[@proto=5]] [[@dialect=lua5.1]]
-- unluac: expect-ast-count [[call]] [[1]] [[@proto=5]] [[@dialect=lua5.2]]
-- unluac: expect-ast-count [[call]] [[1]] [[@proto=5]] [[@dialect=lua5.3]]
-- unluac: expect-ast-count [[call]] [[1]] [[@proto=5]] [[@dialect=lua5.4]]
-- unluac: expect-ast-count [[call]] [[1]] [[@proto=5]] [[@dialect=lua5.5]]
-- unluac: expect-ast-count [[call]] [[1]] [[@proto=5]] [[@dialect=luau]]
-- unluac: expect-ast-count [[call]] [[1]] [[@proto=5]] [[@dialect=luajit]]
-- Luau 的原返回帧直接承接短路值，不应逐轮增加 flag 的局部转交。
-- unluac: expect-ast-count [[local-binding]] [[0]] [[@proto=1]] [[@dialect=luau]]
-- unluac: expect-ast-count [[local-binding]] [[0]] [[@proto=2]] [[@dialect=luau]]
-- unluac: expect-ast-count [[local-binding]] [[1]] [[@proto=3]] [[@dialect=luau]]
-- unluac: expect-ast-count [[local-binding]] [[0]] [[@proto=4]] [[@dialect=luau]]

-- 参数写回的 phi 已经是 ParamRef，内嵌比较仍须在原消费点替换一次。
local function comparison_writeback(value, x, y)
    value = x < y
    value = value and 1 or 0
    return value
end
for x = 0, 2 do
    for y = 0, 2 do
        local actual = comparison_writeback("old", x, y)
        assert(actual == (x < y and 1 or 0))
        print("parameter operand", x, y, actual)
    end
end
-- unluac: expect-not-contains [[unluac error]]
-- unluac: expect-contains [[value = x < y]] [[@debug=retained]]
-- unluac: expect-contains [[value = value and 1 or 0]] [[@debug=retained]]
