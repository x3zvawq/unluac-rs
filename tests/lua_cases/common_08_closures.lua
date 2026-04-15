-- common_08_closures#1: 闭包计数器(upvalue捕获)
local function test_counter()
    local function make_counter(start)
        local value = start

        return function(step)
            value = value + (step or 1)
            return value
        end
    end

    local counter = make_counter(10)
    print("common_08_closures#1", counter(), counter(2), counter())
end

-- common_08_closures#2: 递归局部函数声明
local function test_recursive()
    local function factorial(n)
        local function inner(x, acc)
            if x == 0 then
                return acc
            end

            return inner(x - 1, acc * x)
        end

        return inner(n, 1)
    end

    print("common_08_closures#2", factorial(5), factorial(3))
end

-- common_08_closures#3: 闭包工厂链
local function test_pipeline()
    local function make_pipeline(seed)
        local current = seed

        return function(delta)
            current = current + delta

            return function(scale)
                current = current * scale
                return current
            end
        end
    end

    local pipeline = make_pipeline(2)
    print("common_08_closures#3", pipeline(3)(4), pipeline(1)(2))
end

-- common_08_closures#4: 含副作用闭包步进
local function test_impure_step()
    local function make_counter(start)
        local value = start
        local step_source = {
            index = 0,
            values = {
                [1] = nil,
                [2] = 3,
                [3] = nil,
                [4] = 2,
            },
        }

        function step_source:next()
            self.index = self.index + 1
            return self.values[self.index]
        end

        return function()
            value = value + (step_source:next() or 1)
            return value
        end
    end

    local counter = make_counter(10)
    print("common_08_closures#4", counter(), counter(), counter(), counter())
end

-- common_08_closures#5: 捕获局部变量重绑定
local function test_rebind()
    local x = 1
    local function get()
        return x
    end

    print("common_08_closures#5", get())
    x = 2
    print("common_08_closures#5", get(), x)

    local log = {}
    local function mark(name)
        log[#log + 1] = name
    end

    mark("a")
    print("common_08_closures#5", table.concat(log, ","))
    log = {}
    mark("b")
    print("common_08_closures#5", table.concat(log, ","))
end

-- common_08_closures#6: 表构造器内闭包
local function test_table_ctor()
    local function make_counter()
        local state = {
            current = 1,
        }

        return function(step)
            state.current = state.current + (step or 1)
            return state.current
        end
    end

    local counter = make_counter()
    print("common_08_closures#6", counter(), counter(2), counter())
end

-- common_08_closures#7: 闭包返回对
local function test_return_pair()
    local function closure_test(start_val)
        local counter = start_val

        local function increment(step)
            counter = counter + (step or 1)
            return counter
        end

        local function multiplier(m)
            return counter * m
        end

        return increment, multiplier
    end

    local inc, mul = closure_test(2)
    print("common_08_closures#7", inc(), mul(3), inc(4), mul(2))
end

-- common_08_closures#8: 嵌套闭包工厂
local function test_nested_factory()
    local function factory(seed)
        local offset = seed

        return function(step)
            local base = offset + step

            return function(mult)
                offset = base + mult
                return offset, base * mult
            end
        end
    end

    local stage1 = factory(2)
    local stage2 = stage1(3)
    print("common_08_closures#8", stage2(4))
    print("common_08_closures#8", stage1(1)(2))
end

-- common_08_closures#9: 递归函数槽位
local function test_recursive_slot()
    local function build_runner()
        local out = {}
        local key = 1

        local function step(n)
            if n <= 0 then
                return 0
            end

            return step(n - 1) + 1
        end

        out[key] = step
        return out
    end

    local runner = build_runner()
    print("common_08_closures#9", runner[1](4))
end

-- common_08_closures#10: 循环内break与闭包返回
local function test_loop_break()
    local function collect(limit)
        local funcs = {}
        local i = 0

        while i < limit do
            i = i + 1
            local captured = i * 5

            funcs[#funcs + 1] = function(extra)
                return captured + extra, i
            end

            if i == 3 then
                break
            end
        end

        return funcs, i
    end

    local funcs, final_i = collect(6)
    local a, b = funcs[1](2)
    local c, d = funcs[3](4)

    print("common_08_closures#10", a, b, c, d, final_i, funcs[4] == nil)
end

test_counter()
test_recursive()
test_pipeline()
test_impure_step()
test_rebind()
test_table_ctor()
test_return_pair()
test_nested_factory()
test_recursive_slot()
test_loop_break()
