-- common_05_boolean_expr#1: 算术与逻辑运算符混合
local function test_arith_logic()
    local x = 5 + 3 * 2
    local label = (x > 10) and "gt" or "le"
    local inverted = not (x == 11)

    print("common_05_boolean_expr#1", x, label, inverted)
end

-- common_05_boolean_expr#2: 布尔运算符优先级与括号
local function test_precedence()
    local function judge(a, b, c)
        local value = (a and (b or c)) or ((not b) and c)
        return value and "T" or "F"
    end

    print("common_05_boolean_expr#2", judge(true, false, true), judge(false, true, false), judge(false, false, true))
end

-- common_05_boolean_expr#3: 深层嵌套短路表达式
local function test_boolean_hell()
    local function boolean_hell(a, b, c, d)
        local x = (a and (b or c) and not d) or ((a or d) and (b and c))

        if (x and a) or (not x and b) then
            x = (x == true) and "yes" or (c and "maybe" or "no")
        end

        return x and x or "false"
    end

    print("common_05_boolean_expr#3", boolean_hell(true, false, true, false))
    print("common_05_boolean_expr#3", boolean_hell(false, true, true, false))
    print("common_05_boolean_expr#3", boolean_hell(false, false, true, true))
end

-- common_05_boolean_expr#4: 控制流+闭包+表综合压力测试
local function test_ultimate_mess()
    local function ultimate_mess(root, a, b, c)
        local x = ((a and b) or c) and (b or (c and a)) or (not a and not b)
        local branch = root.branches[a and "t" or "f"]
        local item = branch.items[(b and 1 or 2)]

        return x and "T" or "F", item.value
    end

    local input = {
        branches = {
            t = {
                items = {
                    { value = 11 },
                    { value = 22 },
                },
            },
            f = {
                items = {
                    { value = 33 },
                    { value = 44 },
                },
            },
        },
    }

    print("common_05_boolean_expr#4", ultimate_mess(input, true, false, true))
    print("common_05_boolean_expr#4", ultimate_mess(input, true, true, false))
    print("common_05_boolean_expr#4", ultimate_mess(input, false, false, true))
end

-- common_05_boolean_expr#5: 短路求值的副作用保留
local function test_sc_side_effects()
    local function run_case(left, right)
        local log = {}

        local function mark(name, value)
            log[#log + 1] = name
            return value
        end

        local result = (mark("a", left) and mark("b", right)) or (mark("c", true) and mark("d", "done"))
        return result, table.concat(log, ",")
    end

    local result1, log1 = run_case(false, true)
    local result2, log2 = run_case(true, 0)

    print("common_05_boolean_expr#5", result1, log1)
    print("common_05_boolean_expr#5", result2, log2)
end

-- common_05_boolean_expr#6: 嵌套短路调用与多返回值
local function test_nested_sc()
    local function run_case(first)
        local log = {}

        local function step(name, value)
            log[#log + 1] = name
            return value
        end

        local result = (step("a", first) and (step("b", false) or step("c", "fallback")) and step("d", 8))
            or step("e", 13)

        return result, table.concat(log, ",")
    end

    local result1, log1 = run_case(true)
    local result2, log2 = run_case(false)

    print("common_05_boolean_expr#6", result1, log1)
    print("common_05_boolean_expr#6", result2, log2)
end

test_arith_logic()
test_precedence()
test_boolean_hell()
test_ultimate_mess()
test_sc_side_effects()
test_nested_sc()
