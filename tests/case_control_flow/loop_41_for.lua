-- common_04_generic_for#1: 基础ipairs泛型for
-- 迭代协议保持原生 generic-for，不拆为手写调用循环。
-- unluac: expect-ast-count [[generic-for]] [[1]] [[@dialect=lua5.4]] [[@proto=1]]
local function test_basic_ipairs()
    local colors = { "red", "green", "blue" }
    local parts = {}

    for index, value in ipairs(colors) do
        parts[#parts + 1] = index .. ":" .. value
    end

    print("common_04_generic_for#1", table.concat(parts, "|"))
    assert(table.concat(parts, "|") == "1:red|2:green|3:blue")
end

-- common_04_generic_for#2: 泛型for内break与闭包
local function test_break_closure()
    local funcs = {}

    for i = 1, 5 do
        local captured = i * 10
        funcs[#funcs + 1] = function()
            return captured
        end

        if i == 3 then
            break
        end
    end

    print("common_04_generic_for#2", funcs[1](), funcs[2](), funcs[3](), funcs[4] == nil)
    assert(#funcs == 3 and funcs[1]() == 10 and funcs[2]() == 20 and funcs[3]() == 30)
end

-- common_04_generic_for#3: 迭代中的表修改
local function test_mutator()
    local function generic_for_mutator(list)
        local sum = 0

        for index, value in ipairs(list) do
            local a, b, c = index, value, list[index]
            sum = sum + a + b + c

            if sum > 20 then
                return a, b, c, sum
            end
        end

        return sum
    end

    print("common_04_generic_for#3", generic_for_mutator({ 3, 4, 5, 6 }))
    assert(generic_for_mutator({}) == 0)
    local a, b, c, sum = generic_for_mutator({3, 4, 5, 6})
    assert(a == 3 and b == 5 and c == 5 and sum == 30)
    a, b, c, sum = generic_for_mutator({1})
    assert(a == 3 and b == nil and c == nil and sum == nil)
    assert(generic_for_mutator({1, 4}) == 13)
    a, b, c, sum = generic_for_mutator({4, 4, 0})
    assert(a == 3 and b == 0 and c == 0 and sum == 22)
end

test_basic_ipairs()
test_break_closure()
test_mutator()
-- unluac: expect-ast-count [[local-binding]] [[21]]
-- unluac: expect-ast-count [[local-binding]] [[3]] [[@proto=0]]
-- unluac: expect-ast-count [[generic-for]] [[2]]
-- unluac: expect-ast-count [[numeric-for]] [[1]]
-- 可见循环变量、独立副本与提前返回保持原作用域，不生成状态 carrier 或手写迭代循环。
-- unluac: expect-ast-count [[empty-local]] [[0]]
-- unluac: expect-ast-count [[while]] [[0]]
-- unluac: expect-ast-count [[repeat]] [[0]]
-- unluac: expect-ast-count [[goto]] [[0]]
-- unluac: expect-ast-count [[label]] [[0]]
-- unluac: expect-ast-count [[local-binding]] [[6]] [[@dialect=luau]] [[@proto=5]]
-- unluac: expect-ast-count [[if]] [[1]] [[@dialect=luau]] [[@proto=5]]
-- unluac: expect-ast-count [[local-binding]] [[6]] [[@dialect=luajit]] [[@proto=2]]
-- unluac: expect-ast-count [[if]] [[1]] [[@dialect=luajit]] [[@proto=2]]
