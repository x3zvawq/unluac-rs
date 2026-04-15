-- common_07_return_and_multiret#1: 函数调用与多返回值
local function test_calls_returns()
    local function pair(a, b)
        return a + b, a * b
    end

    local sum, product = pair(4, 6)
    print("common_07_return_and_multiret#1", sum, product)
end

-- common_07_return_and_multiret#2: 返回值截断
local function test_truncation()
    local function returns()
        return "A", "B", "C"
    end

    local values = { returns(), "tail", returns() }

    print("common_07_return_and_multiret#2", table.concat(values, ","))
end

-- common_07_return_and_multiret#3: 变参与尾调用
local function test_vararg_tailcall()
    local unpack_fn = table.unpack or unpack

    local function forward(...)
        local args = { ... }

        local function inner(...)
            return "head", ...
        end

        return inner(unpack_fn(args))
    end

    print("common_07_return_and_multiret#3", forward("x", "y", "z"))
end

-- common_07_return_and_multiret#4: 变参尾部屏障
local function test_vararg_barrier()
    local unpack_fn = table.unpack or unpack

    local function vararg_test(...)
        local args = { ... }

        local function inner(...)
            return "data", ...
        end

        return inner(unpack_fn(args))
    end

    local function wrap(...)
        return { "start", vararg_test(...), "finish" }
    end

    local result = wrap("x", "y")
    print("common_07_return_and_multiret#4", table.concat(result, ","))
end

-- common_07_return_and_multiret#5: 多重返回截断屏障
local function test_trunc_barriers()
    local function return_truncation(...)
        local t = { ..., "barrier", ... }
        local a, b, c = string.find("hello", "ll"), "extra", string.find("world", "or")
        return t, a, b, c
    end

    local t, a, b, c = return_truncation("x", "y")
    print("common_07_return_and_multiret#5", table.concat(t, ","), a, b, c)
end

-- common_07_return_and_multiret#6: 多赋值旋转
local function test_rotation()
    local function values()
        return 10, 20, 30
    end

    local a, b, c = 1, 2, 3
    a, b, c = b, c, values()
    print("common_07_return_and_multiret#6", a, b, c)

    a, b, c = values(), a, b
    print("common_07_return_and_multiret#6", a, b, c)
end

-- common_07_return_and_multiret#7: 调用参数屏障
local function test_call_arg_barrier()
    local function pair()
        return "x", "y"
    end

    local function join(a, b, c, d)
        return table.concat({ a, b, c, d }, ",")
    end

    local result = join(pair(), "mid", pair())
    print("common_07_return_and_multiret#7", result)
end

-- common_07_return_and_multiret#8: select 截断多返回值, select(2, multi_ret()) 应只返回第二个值
local function test_select_truncation()
    local function multi_ret()
        return 1, 2, 3
    end

    local function use_select(...)
        local x = select(2, ...)
        return x
    end

    print("common_07_return_and_multiret#8", use_select(multi_ret()))
end

-- common_07_return_and_multiret#9: 括号包裹 vararg 截断, (...) 应只取第一个值
local function test_paren_vararg_trunc()
    local function truncate(...)
        local a = (...)
        return a
    end

    print("common_07_return_and_multiret#9", truncate(10, 20, 30))
end

test_calls_returns()
test_truncation()
test_vararg_tailcall()
test_vararg_barrier()
test_trunc_barriers()
test_rotation()
test_call_arg_barrier()
test_select_truncation()
test_paren_vararg_trunc()
