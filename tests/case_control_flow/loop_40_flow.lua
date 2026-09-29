-- common_02_control_flow#1: if-elseif-else与提前返回
-- classify 的两个判定保持结构化分支，不引入跳转标签。
-- unluac: expect-ast-count [[if]] [[2]] [[@dialect=lua5.4]] [[@proto=2]]
-- unluac: expect-ast-max [[goto]] [[0]] [[@dialect=lua5.4]] [[@proto=2]]
local function test_if_return()
    local function classify(x)
        if x > 0 then
            return "pos"
        end

        if x == 0 then
            return "zero"
        end

        return "neg"
    end

    print("common_02_control_flow#1", classify(3), classify(0), classify(-2))
    assert(classify(3) == "pos" and classify(0) == "zero" and classify(-2) == "neg")
    assert(classify(0.5) == "pos" and classify(-0.5) == "neg")
end

-- common_02_control_flow#2: while与数值for循环
local function test_while_for()
    local total = 0
    local i = 1

    while i <= 3 do
        total = total + i
        i = i + 1
    end

    for j = 4, 6 do
        total = total + j
    end

    print("common_02_control_flow#2", total)
    assert(total == 21 and i == 4)
end

-- common_02_control_flow#3: 嵌套循环交叉
local function test_nested_mesh()
    local function analyze(limit)
        local out = {}

        for i = 1, limit do
            local j = 0

            while j < 4 do
                j = j + 1

                if (i + j) % 2 == 0 then
                    out[#out + 1] = i * 10 + j
                else
                    repeat
                        out[#out + 1] = i + j
                        break
                    until false
                end

                if j == i then
                    break
                end
            end
        end

        return table.concat(out, "|")
    end

    print("common_02_control_flow#3", analyze(3))
    assert(analyze(0) == "")
    assert(analyze(1) == "11")
    assert(analyze(2) == "11|3|22")
    assert(analyze(3) == "11|3|22|31|5|33")
    assert(analyze(5) == "11|3|22|31|5|33|5|42|7|44|51|7|53|9")
end

-- common_02_control_flow#4: 分支状态传递
local function test_branch_carry()
    local function branch_state(values)
        local state = 0
        local out = {}

        for i = 1, #values do
            local value = values[i]

            if value > 0 then
                state = state + value
            elseif value == 0 then
                state = state + 1
            else
                state = state - value
            end

            out[#out + 1] = state
        end

        return table.concat(out, ",")
    end

    print("common_02_control_flow#4", branch_state({ 2, 0, -3, 1, -1 }))
    assert(branch_state({}) == "")
    assert(branch_state({0, 0}) == "1,2")
    assert(branch_state({-2, -3}) == "2,5")
    assert(branch_state({2, 0, -3, 1, -1}) == "2,3,6,7,8")
end

-- common_02_control_flow#5: 循环尾部guard
local function test_tail_guard()
    local source = {
        [1] = "a",
        [3] = "c",
    }

    local out = {}

    for i = 1, 3 do
        local value = source[i]

        if value then
            out[#out + 1] = value .. i
        end
    end

    print("common_02_control_flow#5", table.concat(out, "|"))
    assert(table.concat(out, "|") == "a1|c3")
end

-- common_02_control_flow#6: while条件中的函数调用
local function test_while_call_cond()
    local items = {10, 20, 30}
    local pos = 0

    local function advance()
        pos = pos + 1
        return items[pos]
    end

    local total = 0

    while advance() do
        total = total + items[pos]
    end

    print("common_02_control_flow#6", total)
    -- 退出前仍须执行最后一次失败的 advance。
    assert(total == 60 and pos == 4)
end

-- common_02_control_flow#7: phi参数重赋值
local function test_phi_reassign()
    -- phi_param_reassign: 当函数参数在分支中被条件改写时, merge 点需要正确
    -- 的 phi 合流。回归测试确保参数寄存器的空 reaching-defs 不会导致 phi 被
    -- 静默拒绝, 从而引发反编译输出丢失原始参数值。

    local function conditional_inc(x)
        if x > 0 then
            x = x + 1
        end
        return x
    end

    print("common_02_control_flow#7", conditional_inc(3), conditional_inc(-1))
    assert(conditional_inc(3) == 4 and conditional_inc(-1) == -1)
    assert(conditional_inc(0) == 0 and conditional_inc(0.5) == 1.5)

end

-- common_02_control_flow#8: 嵌套控制流综合
local function test_nested_cf()
    local function control_flow(x)
        local out = 0

        if x > 10 then
            local a = x * 2
            if a % 3 == 0 then
                out = a
            else
                out = a + 1
            end
        elseif x > 5 then
            repeat
                out = out + 1
                if out == 7 then
                    break
                end
            until out > 10
        else
            for i = 1, 5 do
                out = out + i
            end
        end

        local val = x > 0 and "positive" or "negative"
        return out, val
    end

    local expected = {
        [12] = {24, "positive"}, [11] = {23, "positive"},
        [10] = {7, "positive"}, [8] = {7, "positive"},
        [5] = {15, "positive"}, [3] = {15, "positive"},
        [0] = {15, "negative"}, [-1] = {15, "negative"},
        [255] = {510, "positive"}, [256] = {513, "positive"},
    }
    for _, x in ipairs({ 12, 11, 10, 8, 5, 3, 0, -1, 255, 256 }) do
        local out, val = control_flow(x)
        assert(out == expected[x][1] and val == expected[x][2])
        print("common_02_control_flow#8", x, out, val)
    end
end

-- common_02_control_flow#9: 嵌套 for 循环中 break + 外层条件 break, 内层赋值后 break 不应丢失赋值
local function test_nested_break_assign()
    local function find_target(t)
        local found = nil
        for i = 1, #t do
            if type(t[i]) == "table" then
                for j = 1, #t[i] do
                    if t[i][j] == "target" then
                        found = {i, j}
                        break
                    end
                end
                if found then break end
            end
        end
        return found and (found[1] .. "," .. found[2]) or "not_found"
    end

    print("common_02_control_flow#9", find_target({{1, 2}, {"a", "target", "b"}, {3}}))
    print("common_02_control_flow#9", find_target({{1, 2}, {3, 4}}))
    assert(find_target({}) == "not_found")
    assert(find_target({{1, 2}, {3, 4}}) == "not_found")
    assert(find_target({1, false, "skip", {}, {"target", "target"}}) == "5,1")
    assert(find_target({{"target"}, {"target"}}) == "1,1")
end

test_if_return()
test_while_for()
test_nested_mesh()
test_branch_carry()
test_tail_guard()
test_while_call_cond()
test_phi_reassign()
test_nested_cf()
test_nested_break_assign()
-- SETI/TSETB 的 0..255 边界与负整数键都保留嵌套初始化，不拆成逐字段暂存和后续赋值。
-- JIT 的 [0] 会产生数组预分配，但这些显式数字键仍是 record；寄存器键在值之后准备。
-- unluac: expect-ast-count [[local-binding]] [[6]] [[@proto=3]] [[@dialect=luajit]]
-- unluac: expect-ast-count [[assign]] [[0]] [[@proto=3]] [[@dialect=luajit]]
-- unluac: expect-ast-count [[local-binding]] [[6]] [[@proto=13]] [[@dialect=lua5.4]]
-- unluac: expect-ast-count [[local-binding]] [[6]] [[@proto=13]] [[@dialect=lua5.5]]
-- unluac: expect-ast-count [[assign]] [[0]] [[@proto=13]] [[@dialect=lua5.4]]
-- unluac: expect-ast-count [[assign]] [[0]] [[@proto=13]] [[@dialect=lua5.5]]
-- Luau 的 1..256 为内嵌键，0/负数先准备键再创建值；完整 record 恢复后无字段暂存赋值。
-- unluac: expect-ast-count [[local-binding]] [[6]] [[@proto=13]] [[@dialect=luau]]
-- unluac: expect-ast-count [[assign]] [[0]] [[@proto=13]] [[@dialect=luau]]
-- CALL 结果的比较参数与嵌套数组属于同一 assert 帧，不先物化 subject 或数组元素。
-- unluac: expect-ast-count [[local-binding]] [[1]] [[@proto=15]] [[@dialect=luau]]
-- unluac: expect-ast-count [[assign]] [[0]] [[@proto=15]] [[@dialect=luau]]
-- 模块计数不依赖 LuaJIT 与 PUC 不同的子原型顺序；额外固定已发现的参数和查表退化。
-- 5.2+ 的跨类型比较可调用元方法；val 必须在 return 的首项 COPY 之前求值，
-- 否则会提前覆盖 a 的残根。roots_15_return_selection_snapshot 固定这个 GC 区别。
-- unluac: expect-ast-count [[local-binding]] [[44]] [[@dialect=lua5.1]]
-- unluac: expect-ast-count [[local-binding]] [[45]] [[@dialect=lua5.2]]
-- unluac: expect-ast-count [[local-binding]] [[45]] [[@dialect=lua5.3]]
-- unluac: expect-ast-count [[local-binding]] [[45]] [[@dialect=lua5.4]]
-- unluac: expect-ast-count [[local-binding]] [[45]] [[@dialect=lua5.5]]
-- JIT 的取模结果残根须存活至选择表达式之后，见 roots_16_jit_return_remainder_root。
-- unluac: expect-ast-count [[local-binding]] [[45]] [[@dialect=luajit]]
-- unluac: expect-ast-count [[local-binding]] [[4]] [[@proto=4]] [[@dialect=luajit]]
-- unluac: expect-ast-count [[local-binding]] [[44]] [[@dialect=luau]]
-- unluac: expect-ast-count [[local-binding]] [[4]] [[@proto=14]] [[@dialect=lua5.2]]
-- unluac: expect-ast-count [[local-binding]] [[4]] [[@proto=14]] [[@dialect=lua5.3]]
-- unluac: expect-ast-count [[local-binding]] [[4]] [[@proto=14]] [[@dialect=lua5.4]]
-- unluac: expect-ast-count [[local-binding]] [[4]] [[@proto=14]] [[@dialect=lua5.5]]
-- unluac: expect-ast-count [[local-binding]] [[9]] [[@proto=0]]
-- unluac: expect-ast-count [[local-binding]] [[0]] [[@proto=12]] [[@dialect=lua5.1]]
-- unluac: expect-ast-count [[local-binding]] [[0]] [[@proto=12]] [[@dialect=luau]]
-- unluac: expect-ast-count [[local-binding]] [[3]] [[@proto=16]] [[@dialect=lua5.4]]
-- unluac: expect-ast-count [[local-binding]] [[3]] [[@proto=16]] [[@dialect=luau]]
-- unluac: expect-ast-count [[local-binding]] [[3]] [[@proto=2]] [[@dialect=luajit]]
-- unluac: expect-ast-count [[numeric-for]] [[7]]
-- unluac: expect-ast-count [[generic-for]] [[1]]
-- unluac: expect-ast-count [[while]] [[3]]
