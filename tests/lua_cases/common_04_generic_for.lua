-- common_04_generic_for#1: 基础ipairs泛型for
local function test_basic_ipairs()
    local colors = { "red", "green", "blue" }
    local parts = {}

    for index, value in ipairs(colors) do
        parts[#parts + 1] = index .. ":" .. value
    end

    print("common_04_generic_for#1", table.concat(parts, "|"))
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
end

test_basic_ipairs()
test_break_closure()
test_mutator()
