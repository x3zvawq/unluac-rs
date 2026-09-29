-- common_03_repeat_until#1: 基础repeat-until循环
-- 基础尾条件循环应保持 repeat，而不是引入条件 carrier。
-- unluac: expect-ast-count [[repeat]] [[1]] [[@dialect=lua5.4]] [[@proto=1]]
-- unluac: expect-ast-max [[empty-local]] [[0]] [[@dialect=lua5.4]] [[@proto=1]]
-- unluac: expect-ast-count [[repeat]] [[6]]
-- unluac: expect-ast-count [[while]] [[1]]
-- unluac: expect-ast-count [[local-binding]] [[34]]
-- unluac: expect-ast-count [[local-binding]] [[3]] [[@dialect=lua5.4]] [[@proto=10]]
-- unluac: expect-ast-count [[empty-local]] [[0]] [[@dialect=lua5.4]] [[@proto=10]]
-- unluac: expect-ast-count [[local-binding]] [[3]] [[@dialect=luau]] [[@proto=10]]
-- unluac: expect-ast-count [[empty-local]] [[0]] [[@dialect=luau]] [[@proto=10]]
-- unluac: expect-ast-count [[local-binding]] [[3]] [[@dialect=luajit]] [[@proto=1]]
-- unluac: expect-ast-count [[empty-local]] [[0]] [[@dialect=luajit]] [[@proto=1]]
local function test_basic_repeat()
    local i = 0
    local values = {}

    repeat
        i = i + 1
        values[i] = i * i
    until i >= 4

    assert(i == 4 and #values == 4 and table.concat(values, ",") == "1,4,9,16")
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

    assert(i == 3 and #t == 3 and t[1] == 1 and t[2] == 4 and t[3] == 9)
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
    assert(#funcs == 6)
    assert(funcs[1]() == 8 and funcs[2]() == 10 and funcs[3]() == 12)
    assert(funcs[4]() == 14 and funcs[5]() == 16 and funcs[6]() == 18)
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

    assert(i == 4 and sum == 22)
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
    assert(#funcs == 6 and a1 == 22 and a2 == 3 and b1 == 23 and b2 == 3 and c1 == 25 and c2 == 3)

    print("common_03_repeat_until#5", a1, a2, b1, b2, c1, c2)
    a1, a2 = funcs[4](0)
    b1, b2 = funcs[5](0)
    c1, c2 = funcs[6](0)
    assert(a1 == 22 and a2 == 3 and b1 == 23 and b2 == 3 and c1 == 23 and c2 == 3)
end

test_basic_repeat()
test_cond_prefix()
test_closure_break()
test_break_value()
test_interleave()

-- 尾条件调用更新同一个捕获 cell；提前 break 必须跳过更新，正常出口不能写回旧快照。
do
    local function captured_tail(early)
        local rounds, n = 0, 0
        local function step(value)
            n = n + 10
            return value
        end
        repeat
            rounds = rounds + 1
            if rounds ~= 1 then
                n = n + 1
                if early then break end
            end
        until step(rounds > 2)
        return rounds, n
    end
    local dispatch = {captured_tail}
    local rounds, n = dispatch[1](false)
    assert(rounds == 3 and n == 32)
    rounds, n = dispatch[1](true)
    assert(rounds == 2 and n == 11)
    print("captured-tail", rounds, n)
end
