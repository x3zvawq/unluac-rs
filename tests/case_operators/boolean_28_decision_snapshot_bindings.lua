-- 直接寄存器读取可见右侧调用后的值；GETUPVAL 的显式读取必须保留调用前的快照。
-- O2 可复制三个内联调用中的 read 闭包；其余配置保留九个源码函数。
-- unluac: expect-ast-min [[function]] [[9]]
-- unluac: expect-ast-max [[function]] [[12]]
-- unluac: expect-ast-count [[goto]] [[0]]
-- compare 的输入快照、两次选择结果和最终结果已足够；上值算术写回不另占持续声明。
-- unluac: expect-ast-max [[local-binding]] [[4]] [[@proto=9]] [[@dialect=luau]] [[@variant=O2]] [[@debug=stripped]]
-- 比较中的算术仍在原参数槽执行；三结果调用和断言不留下调用帧中转声明。
-- unluac: expect-ast-max [[local-binding]] [[11]] [[@proto=0]] [[@dialect=luajit]] [[@debug=retained]]
-- unluac: expect-contains [[local result, value, calls = stable(active, selected, expected)]] [[@dialect=luajit]] [[@debug=retained]]
-- O2 保留三个内联闭包及跨作用域结果；CLOSE 后的算术不得继续制造预写和声明副本。
-- unluac: expect-ast-max [[local-binding]] [[50]] [[@proto=0]] [[@dialect=luau]] [[@variant=O2]] [[@debug=retained]]
local function stable(enabled, selected, seed)
    local value = seed + 0
    local calls = 0
    local function read()
        calls = calls + 1
        return selected == calls
    end
    local result = enabled and value == ((read() and 1 or 2) == (read() and 1 or 2) and 7 or 8)
    return result, value, calls
end

local function captured_local(enabled, selected, seed)
    local value = seed + 0
    local calls = 0
    local function read()
        calls = calls + 1
        value = value + 10
        return selected == calls
    end
    local result = enabled and value == ((read() and 1 or 2) == (read() and 1 or 2) and 7 or 8)
    return result, value, calls
end

local function captured_parameter(enabled, selected, value)
    local calls = 0
    local function read()
        calls = calls + 1
        value = value + 10
        return selected == calls
    end
    local result = enabled and value == ((read() and 1 or 2) == (read() and 1 or 2) and 7 or 8)
    return result, value, calls
end

local function captured_upvalue(enabled, selected, seed)
    local value = seed + 0
    local calls = 0
    local function read()
        calls = calls + 1
        value = value + 10
        return selected == calls
    end
    local function compare()
        return enabled and value == ((read() and 1 or 2) == (read() and 1 or 2) and 7 or 8)
    end
    -- 经表调用保留上值读取边界，Luau O2 不能把 compare 内联成父级寄存器读取。
    local comparisons = { compare }
    local result = comparisons[1]()
    return result, value, calls
end

for selected = 0, 3 do
    local expected = 7
    if selected == 1 or selected == 2 then expected = 8 end
    for enabled = 0, 1 do
        local active = enabled == 1
        local result, value, calls = stable(active, selected, expected)
        assert(result == active and value == expected and calls == enabled * 2)
        result, value, calls = captured_local(active, selected, expected)
        assert(result == false and value == expected + enabled * 20 and calls == enabled * 2)
        result, value, calls = captured_parameter(active, selected, expected)
        assert(result == false and value == expected + enabled * 20 and calls == enabled * 2)
        result, value, calls = captured_upvalue(active, selected, expected)
        assert(result == active and value == expected + enabled * 20 and calls == enabled * 2)
    end
end
print("decision-snapshot-bindings", "ok")
