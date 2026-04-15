-- common_01_basics#1: 多赋值与局部变量初始化
local function test_assignments()
    local a, b, c = "alpha", 42, true
    local x, y, z = 1, 2, 3

    print("common_01_basics#1", a, b, c, x + y + z)
end

-- common_01_basics#2: do-end块作用域与变量遮蔽
local function test_locals_and_blocks()
    local name = "outer"

    do
        local name = "inner"
        local value = name .. "-block"
        print("common_01_basics#2", name, value)
    end

    print("common_01_basics#2", name)
end

-- common_01_basics#3: 表引用别名在循环中的修改
local function test_alias_mutation()
    local t = { 1, 2 }
    local cached = t[1]

    for i = 1, 3 do
        t[1] = i + 10
    end

    print("common_01_basics#3", cached, t[1], t[2])
end

-- common_01_basics#4: 多层嵌套变量遮蔽与条件返回
local function test_shadowed_locals()
    local function choose(flag)
        local value = "root"

        if flag then
            local value = "branch"
            if #value > 0 then
                print("common_01_basics#4", value .. "-if")
            end

            value = value .. "-mut"
            return value
        end

        do
            local value = "else"
            print("common_01_basics#4", value)
        end

        return value
    end

    print("common_01_basics#4", choose(true), choose(false))
end

-- common_01_basics#5: 数值for循环控制变量不可变性
local function test_for_rebound()
    local start, stop, step = 1, 7, 2
    local values = {}

    for i = start, stop, step do
        values[#values + 1] = i
        start = 100
        step = 100
    end

    print("common_01_basics#5", table.concat(values, ","), start, step)
end

test_assignments()
test_locals_and_blocks()
test_alias_mutation()
test_shadowed_locals()
test_for_rebound()
