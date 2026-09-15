-- unluac: expect-not-contains [[p5_0 or p5_3 and p5_1 and p5_2) and p5_1 and p5_2]]
-- unluac: expect-not-contains [[p10_0 or p10_3 and p10_1 and p10_2) and p10_1 and p10_2]]
-- 两个循环内尚未恢复的 assert 帧不能阻断循环外的独立帧；此上限也检查再生成。
-- unluac: expect-max-count [[ = assert]] [[2]] [[@dialect=lua5.4]]
-- JIT 循环的比较参数与结果查表保留完整 assert，只留下预期表和身份观察表。
-- unluac: expect-ast-count [[local-decl]] [[1]] [[@proto=11]] [[@dialect=luajit]]
-- unluac: expect-ast-count [[local-decl]] [[2]] [[@proto=9]] [[@dialect=luajit]]
-- 未融合模板的 hash 展示顺序必须稳定；也允许后续直接恢复完整构造器。
-- unluac: expect-not-contains [[{ t = nil, f = nil }]] [[@dialect=luajit]]
-- judge 的第二个参数只需两次读取和一次形参声明；再生成不得复制共同条件尾。
-- unluac: expect-max-count [[p3_1]] [[3]] [[@dialect=luau]]
-- Luau 的优先级循环只保留 expected 表，不拆分比较参数、judge callee 和 assert 参数。
-- unluac: expect-ast-count [[local-decl]] [[1]] [[@proto=2]] [[@dialect=luau]]
-- judge 的纯值选择应直接返回，不拆成局部中转；LuaJIT 的兄弟 proto 顺序相反。
-- unluac: expect-ast-count [[local-decl]] [[0]] [[@proto=3]] [[@dialect=lua5.1]]
-- unluac: expect-ast-count [[local-decl]] [[0]] [[@proto=3]] [[@dialect=lua5.2]]
-- unluac: expect-ast-count [[local-decl]] [[0]] [[@proto=3]] [[@dialect=lua5.3]]
-- unluac: expect-ast-count [[local-decl]] [[0]] [[@proto=3]] [[@dialect=lua5.4]]
-- unluac: expect-ast-count [[local-decl]] [[0]] [[@proto=3]] [[@dialect=lua5.5]]
-- unluac: expect-ast-count [[local-decl]] [[0]] [[@proto=12]] [[@dialect=luajit]]
-- unluac: expect-ast-count [[local-decl]] [[0]] [[@proto=3]] [[@dialect=luau]]
-- 短路 CALL 的 callee 准备属于整棵值表达式；只保留 trace 与结果两个普通声明。
-- unluac: expect-ast-count [[local-decl]] [[2]] [[@proto=9]] [[@dialect=lua5.1]]
-- unluac: expect-ast-count [[local-decl]] [[2]] [[@proto=12]] [[@dialect=lua5.1]]
-- unluac: expect-ast-count [[local-decl]] [[2]] [[@proto=9]] [[@dialect=lua5.2]]
-- unluac: expect-ast-count [[local-decl]] [[2]] [[@proto=12]] [[@dialect=lua5.2]]
-- unluac: expect-ast-count [[local-decl]] [[2]] [[@proto=9]] [[@dialect=lua5.3]]
-- unluac: expect-ast-count [[local-decl]] [[2]] [[@proto=12]] [[@dialect=lua5.3]]
-- unluac: expect-ast-count [[local-decl]] [[2]] [[@proto=9]] [[@dialect=lua5.4]]
-- unluac: expect-ast-count [[local-decl]] [[2]] [[@proto=12]] [[@dialect=lua5.4]]
-- unluac: expect-ast-count [[local-decl]] [[2]] [[@proto=9]] [[@dialect=lua5.5]]
-- unluac: expect-ast-count [[local-decl]] [[2]] [[@proto=12]] [[@dialect=lua5.5]]
-- unluac: expect-ast-count [[local-decl]] [[2]] [[@proto=5]] [[@dialect=luajit]]
-- unluac: expect-ast-count [[local-decl]] [[2]] [[@proto=2]] [[@dialect=luajit]]
-- Luau 短路树保留原逻辑结果槽，首个 predicate CALL 的高槽准备不形成独立别名。
-- unluac: expect-ast-count [[local-decl]] [[2]] [[@proto=9]] [[@dialect=luau]]
-- unluac: expect-ast-count [[local-decl]] [[2]] [[@proto=12]] [[@dialect=luau]]

-- common_05_boolean_expr#1: 算术与逻辑运算符混合
local function test_arith_logic()
    local x = 5 + 3 * 2
    local label = (x > 10) and "gt" or "le"
    local inverted = not (x == 11)

    assert(x == 11 and label == "gt" and inverted == false)
    print("common_05_boolean_expr#1", x, label, inverted)
end

-- common_05_boolean_expr#2: 布尔运算符优先级与括号
local function test_precedence()
    local function judge(a, b, c)
        local value = (a and (b or c)) or ((not b) and c)
        return value and "T" or "F"
    end

    print("common_05_boolean_expr#2", judge(true, false, true), judge(false, true, false), judge(false, false, true))

    -- a/b/c 按从高到低的二进制位枚举；预期表不重复被测逻辑式。
    local expected = { "F", "T", "F", "F", "F", "T", "T", "T" }
    for bits = 0, 7 do
        assert(judge(bits >= 4, bits % 4 >= 2, bits % 2 == 1) == expected[bits + 1])
    end
    assert(judge(0, false, nil) == "F")
    assert(judge("", "value", false) == "T")
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

    -- 第八项是 Boolean true，不能把它与其它分支的字符串混为一类。
    local expected = {
        "false", "false", "false", "false", "no", "no", "maybe", true,
        "false", "false", "yes", "false", "yes", "no", "yes", "yes",
    }
    for bits = 0, 15 do
        assert(boolean_hell(bits >= 8, bits % 8 >= 4, bits % 4 >= 2, bits % 2 == 1) == expected[bits + 1])
    end
    local token = {}
    assert(boolean_hell(false, true, token, true) == token)
    assert(boolean_hell(true, true, token, true) == "maybe")
    assert(boolean_hell(0, true, true, true) == "yes")
    assert(boolean_hell(true, true, 0, true) == "maybe")
    assert(boolean_hell(nil, true, true, nil) == "maybe")
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

    local expected_labels = { "T", "T", "F", "T", "F", "T", "T", "T" }
    local expected_items = { 44, 44, 33, 33, 22, 22, 11, 11 }
    for bits = 0, 7 do
        local label, value = ultimate_mess(input, bits >= 4, bits % 4 >= 2, bits % 2 == 1)
        assert(label == expected_labels[bits + 1] and value == expected_items[bits + 1])
    end
    local label, value = ultimate_mess(input, 0, "", nil)
    assert(label == "T" and value == 11)
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

    assert(result1 == "done" and log1 == "a,c,d")
    assert(result2 == 0 and log2 == "a,b")

    print("common_05_boolean_expr#5", result1, log1)
    print("common_05_boolean_expr#5", result2, log2)

    local token = {}
    local cases = {
        { nil, true, "done", "a,c,d" },
        { true, nil, "done", "a,b,c,d" },
        { true, false, "done", "a,b,c,d" },
        { true, "", "", "a,b" },
        { true, token, token, "a,b" },
    }
    for _, row in ipairs(cases) do
        local result, log = run_case(row[1], row[2])
        assert(result == row[3] and log == row[4])
    end
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

    assert(result1 == 8 and log1 == "a,b,c,d")
    assert(result2 == 13 and log2 == "a,e")

    print("common_05_boolean_expr#6", result1, log1)
    print("common_05_boolean_expr#6", result2, log2)

    local cases = {
        { nil, 13, "a,e" },
        { 0, 8, "a,b,c,d" },
        { "", 8, "a,b,c,d" },
        { {}, 8, "a,b,c,d" },
    }
    for _, row in ipairs(cases) do
        local result, log = run_case(row[1])
        assert(result == row[2] and log == row[3])
    end
end

test_arith_logic()
test_precedence()
test_boolean_hell()
test_ultimate_mess()
test_sc_side_effects()
test_nested_sc()
