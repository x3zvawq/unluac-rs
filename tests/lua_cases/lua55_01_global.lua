-- lua55_01_global#1: global关键字基础
local function test_global_basic()
    global none, print
    global counter, label = 9, "seed"

    global function step(delta)
        counter = counter * 2 + delta
        return label .. ":" .. counter
    end

    local first = step(3)
    local second = step(5)

    print("lua55_01_global#1", first, second, counter, label)
end

-- lua55_01_global#2: global函数捕获
local function test_global_capture()
    global none, print
    global outer_prefix, global_bias = "G", 4
    global emit

    local function install(tag)
        local prefix = tag .. ":" .. outer_prefix
        local hop = global_bias * #tag

        global function emit(x)
            local mixed = x * hop + #prefix
            return prefix, mixed, outer_prefix .. ":" .. global_bias
        end
    end

    install("ax")
    global_bias = global_bias + 3
    outer_prefix = outer_prefix .. "!"

    local a1, b1, c1 = emit(2)
    local a2, b2, c2 = emit(5)

    print("lua55_01_global#2", a1, b1, c1, a2, b2, c2)
end

-- lua55_01_global#3: const门控
local function test_const_gate()
    global none, print
    global score = 6

    local function inspect(tag)
        local shadow = #tag + 1

        do
            global<const> *
            local left = math.max(shadow, score)
            local right = tostring(shadow) .. ":" .. tostring(score)
            return left, right
        end
    end

    local a, b = inspect("abc")
    score = score + a

    print("lua55_01_global#3", a, b, score)
end

test_global_basic()
test_global_capture()
test_const_gate()
