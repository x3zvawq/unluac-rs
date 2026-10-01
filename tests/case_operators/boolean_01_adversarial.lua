-- regress_01_boolean_adversarial#1: 循环内 and/or 链遇到 nil/false 元素, t[i] and t[i]>0 and t[i] or 0
-- unluac: expect-ast-min [[numeric-for]] [[1]]
-- unluac: expect-ast-count [[function]] [[5]]
-- unluac: expect-ast-max [[local-binding]] [[2]] [[@proto=2]]
-- 此样例的求和函数在 LuaJIT 中为 proto#5，其余方言为 proto#2。
-- unluac: expect-ast-count [[if]] [[0]] [[@proto=2]] [[@dialect=lua5.1]]
-- unluac: expect-ast-count [[if]] [[0]] [[@proto=2]] [[@dialect=lua5.2]]
-- unluac: expect-ast-count [[if]] [[0]] [[@proto=2]] [[@dialect=lua5.3]]
-- unluac: expect-ast-count [[if]] [[0]] [[@proto=2]] [[@dialect=lua5.4]]
-- unluac: expect-ast-count [[if]] [[0]] [[@proto=2]] [[@dialect=lua5.5]]
-- unluac: expect-ast-count [[if]] [[0]] [[@proto=2]] [[@dialect=luau]]
-- unluac: expect-ast-count [[if]] [[0]] [[@proto=5]] [[@dialect=luajit]]
-- unluac: expect-ast-max [[local-binding]] [[2]] [[@proto=5]]
local function test_sc_loop_nil()
    local function sum_positive(t, count)
        local result = 0
        for i = 1, count do
            result = result + (t[i] and t[i] > 0 and t[i] or 0)
        end
        return result
    end

    print("regress_01_boolean_adversarial#1", sum_positive({1, nil, -2, 3, false, 5}, 6))
    -- 显式长度保证 nil 元素确实被访问；代理逐次观察短路链中的重复索引。
    local data = {1, nil, -2, 3, false, 5, 0}
    local reads = {}
    local dynamic, ordinal = false, 0
    local proxy = setmetatable({}, { __index = function(_, key)
        reads[#reads + 1] = key
        if dynamic then
            ordinal = ordinal + 1
            if ordinal == 1 then return true end
            if ordinal == 2 then return 1 end
        end
        return data[key]
    end })
    assert(sum_positive(proxy, 7) == 9)
    assert(sum_positive(proxy, 0) == 0)
    assert(table.concat(reads, ",") == "1,1,1,2,3,3,4,4,4,5,6,6,6,7,7")
    -- 前两次读取只作谓词，第三次才取值；同一键可依次返回不同类型。
    -- 第三次为 false/nil 时仍须执行外层 or，不能保留早先的 truthy 快照。
    dynamic = true
    local alternatives = {7, false}
    for index = 1, 3 do
        data[1] = alternatives[index]
        ordinal, reads = 0, {}
        local expected = alternatives[index] or 0
        assert(sum_positive(proxy, 1) == expected)
        assert(ordinal == 3 and table.concat(reads, ",") == "1,1,1")
    end
end

-- regress_01_boolean_adversarial#2: elseif 分支内 and/or 三元模拟, a>b and a or b 赋给局部变量
-- unluac: expect-ast-min [[if]] [[1]]
-- 合流的同身份分量不是一次额外源码写回。
-- unluac: expect-not-contains [[r5_0, "multiplied"]]
-- unluac: expect-not-contains [[r5_1, "multiplied"]]
-- unluac: expect-not-contains [[r2_0, "multiplied"]]
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
    local value, extra, trailing = compute("add", 3, 4)
    assert(value == 7 and extra == "" and trailing == nil)
    value, extra, trailing = compute("mul", -3, 4)
    assert(value == -12 and extra == "multiplied" and trailing == nil)
    value, extra, trailing = compute("max", 8, 4)
    assert(value == 8 and extra == "compared" and trailing == nil)
    value, extra, trailing = compute("max", 4, 4)
    assert(value == 4 and extra == "compared" and trailing == nil)
    value, extra, trailing = compute(nil, 3, 4)
    assert(value == 0 and extra == "unknown" and trailing == nil)
end

test_sc_loop_nil()
test_ternary_in_elseif()
