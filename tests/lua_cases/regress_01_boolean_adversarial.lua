-- regress_01_boolean_adversarial#1: 循环内 and/or 链遇到 nil/false 元素, t[i] and t[i]>0 and t[i] or 0
local function test_sc_loop_nil()
    local function sum_positive(t)
        local result = 0
        for i = 1, #t do
            result = result + (t[i] and t[i] > 0 and t[i] or 0)
        end
        return result
    end

    print("regress_01_boolean_adversarial#1", sum_positive({1, nil, -2, 3, false, 5}))
end

-- regress_01_boolean_adversarial#2: elseif 分支内 and/or 三元模拟, a>b and a or b 赋给局部变量
local function test_ternary_in_elseif()
    local function compute(mode, a, b)
        local result
        local extra = ""
        if mode == "add" then
            result = a + b
        elseif mode == "mul" then
            result = a * b
            extra = "multiplied"
        elseif mode == "max" then
            result = a > b and a or b
            extra = "compared"
        else
            result = 0
            extra = "unknown"
        end
        return result, extra
    end

    print("regress_01_boolean_adversarial#2", compute("add", 3, 4))
    print("regress_01_boolean_adversarial#2", compute("mul", 3, 4))
    print("regress_01_boolean_adversarial#2", compute("max", 3, 4))
    print("regress_01_boolean_adversarial#2", compute("other", 3, 4))
end

test_sc_loop_nil()
test_ternary_in_elseif()
