-- 常量选择可越过无 binding 写入的 suffix；短路路径、错误与元方法次数保持不变。
local function describe(value)
    local prefix = value and "present" or "missing"
    local suffix = value ~= nil and (value > 10 and "large" or "small") or "none"
    return prefix .. ":" .. suffix
end

assert(describe(nil) == "missing:none")
assert(describe(-1) == "present:small")
assert(describe(0) == "present:small")
assert(describe(10) == "present:small")
assert(describe(11) == "present:large")
assert(describe(1 / 0) == "present:large")
assert(describe(0 / 0) == "present:small")
assert(not pcall(describe, false))
assert(not pcall(describe, true))
assert(not pcall(describe, "12"))
assert(not pcall(describe, {}))

local function check_metatable(comparison_result, expected)
    local weak = setmetatable({}, {__mode = "v"})
    local comparisons = 0
    local unexpected_calls = 0
    local function unexpected()
        unexpected_calls = unexpected_calls + 1
        error("truthiness, nil equality and string results must not invoke object metamethods")
    end
    local mt = {
        __eq = unexpected, __concat = unexpected, __index = unexpected,
        __lt = function(left, right)
            comparisons = comparisons + 1
            assert(left == 10 and right == weak.value)
            left, right = nil, nil
            collectgarbage("collect")
            collectgarbage("collect")
            assert(weak.value ~= nil, "describe parameter must remain rooted during comparison")
            return comparison_result
        end,
    }
    local function make()
        local value = setmetatable({}, mt)
        weak.value = value
        return value
    end
    local ok, result = pcall(function() return describe(make()) end)
    assert(unexpected_calls == 0)
    if ok then
        assert(result == expected and comparisons == 1)
    else
        -- 部分 VM 拒绝 table 与 number 混合比较，不能把其它 VM 的元方法规则外推到它们。
        assert(comparisons == 0)
    end
    print("comparison", ok, comparisons)
end
check_metatable(true, "present:large")
check_metatable(false, "present:small")
check_metatable(nil, "present:small")
check_metatable(0, "present:large")

-- 首参被引用捕获并实际改变时，prefix 必须保留原声明点快照。
local function captured(value)
    local prefix = value and "present" or "missing"
    local function change()
        value = false
        return "suffix"
    end
    local suffix = change()
    return prefix .. ":" .. suffix
end
assert(captured(true) == "present:suffix")
print("regress_557_short_circuit_constant_snapshot", "OK")
