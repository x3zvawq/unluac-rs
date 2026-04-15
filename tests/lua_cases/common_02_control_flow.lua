-- common_02_control_flow#1: if-elseif-else与提前返回
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

    for _, x in ipairs({ 12, 8, 3, -1 }) do
        local out, val = control_flow(x)
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
