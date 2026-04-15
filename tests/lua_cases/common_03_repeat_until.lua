-- common_03_repeat_until#1: 基础repeat-until循环
local function test_basic_repeat()
    local i = 0
    local values = {}

    repeat
        i = i + 1
        values[i] = i * i
    until i >= 4

    print("common_03_repeat_until#1", table.concat(values, ","))
end

-- common_03_repeat_until#2: repeat条件前缀表达式
local function test_cond_prefix()
    local t = {}
    local i = 0

    repeat
        i = i + 1
        t[i] = i * i
    until t[i] >= 9

    print("common_03_repeat_until#2", i, t[1], t[2], t[3])
end

-- common_03_repeat_until#3: repeat-until内闭包与运行时
local function test_closure_break()
    local function repeat_until_nightmare()
        local funcs = {}
        local i = 0

        repeat
            i = i + 1
            local captured_var = i * 2

            funcs[i] = function()
                return captured_var + i
            end

            if captured_var > 10 and i % 2 == 0 then
                break
            end
        until captured_var > 15

        return funcs
    end

    local funcs = repeat_until_nightmare()
    print("common_03_repeat_until#3", funcs[1](), funcs[3](), funcs[6](), funcs[7] == nil)
end

-- common_03_repeat_until#4: repeat内break的值流
local function test_break_value()
    local i = 0
    local sum = 0

    repeat
        i = i + 1

        if i % 2 == 0 then
            sum = sum + i * 3
        else
            sum = sum + i
        end

        if sum > 10 then
            break
        end
    until i >= 6

    print("common_03_repeat_until#4", i, sum)
end

-- common_03_repeat_until#5: while与repeat交错闭包
local function test_interleave()
    local function run()
        local i = 0
        local out = {}

        while i < 3 do
            i = i + 1
            local base = i

            repeat
                out[#out + 1] = function(delta)
                    return base + delta, i
                end
                base = base + 10
            until base > i + 10
        end

        return out
    end

    local funcs = run()
    local a1, a2 = funcs[1](1)
    local b1, b2 = funcs[2](2)
    local c1, c2 = funcs[3](3)

    print("common_03_repeat_until#5", a1, a2, b1, b2, c1, c2)
end

test_basic_repeat()
test_cond_prefix()
test_closure_break()
test_break_value()
test_interleave()
