-- lua53_01#1: 位运算与整除
-- unluac: expect-ast-count [[function]] [[18]]
-- unluac: expect-ast-count [[numeric-for]] [[4]]
-- unluac: expect-ast-count [[while]] [[1]]
-- 索引写入和多结果返回的准备不能成为额外的源码绑定。
-- unluac: expect-ast-max [[local-binding]] [[4]] [[@proto=4]]
-- unluac: expect-ast-max [[local-binding]] [[7]] [[@proto=6]]
-- unluac: expect-ast-max [[local-binding]] [[5]] [[@proto=8]]
-- unluac: expect-ast-max [[local-binding]] [[3]] [[@proto=11]]
-- unluac: expect-ast-count [[local-binding]] [[0]] [[@proto=14]]
-- unluac: expect-ast-max [[local-binding]] [[3]] [[@proto=18]]
-- 运算准备不能复用结果变量形成接棒赋值；只保留分支状态更新和最终字段写。
-- unluac: expect-ast-count [[assign]] [[3]] [[@proto=8]]
-- unluac: expect-ast-count [[assign]] [[3]] [[@proto=18]]
local function test_bitwise_idiv()
    local a = (15 // 2) + (5 << 1)
    local b = (0x3F & 0x0F) ~ 0x02
    local c = 20 >> 2
    assert(a == 17 and b == 13 and c == 5 and math.type(a) == "integer")

    print("lua53_01#1", a, b, c)
end

-- lua53_01#2: 位运算闭包交叉
local function test_closure_mesh()
    local function make_mixer(seed, stride)
        local mask = ((seed << 2) | 0x35) ~ (stride & 0x0F)
        local history = {}

        return function(list)
            local acc = mask

            for i = 1, #list do
                local value = list[i]
                local mixed = (((value << (i % 3)) | acc) ~ (seed >> (i - 1))) & 0xFF

                if (mixed & 1) == 0 then
                    acc = ((acc ~ mixed) << 1) & 0xFF
                else
                    acc = ((acc | mixed) >> 1) ~ stride
                end

                history[#history + 1] = acc ~ i
            end

            return acc, history[#history - 1], history[#history]
        end
    end

    local run_a = make_mixer(0x2D, 0x13)
    local run_b = make_mixer(0x19, 0x05)

    print("lua53_01#2", run_a({ 3, 9, 12, 17 }))
    print("lua53_01#2", run_b({ 8, 1, 14 }))
    -- 空输入不追加 history，仍返回上一次调用留下的两个尾项。
    assert(run_a({}) == 182 and select(2, run_a({})) == 39 and select(3, run_a({})) == 4)
    assert(run_b({}) == 112 and select(2, run_b({})) == 27 and select(3, run_b({})) == 10)
    assert(select("#", run_a({})) == 3)
end

-- lua53_01#3: 整除浮点分支
local function test_idiv_float()
    local function analyze(values)
        local score = 0
        local frac = 0.0

        for i = 1, #values do
            local value = values[i]
            local floor = (value * 3 + i) // 2
            local ratio = (value * 3 + i) / 2
            local mod = (floor + i) % 5

            if mod == 0 or (ratio - floor) > 0.4 then
                score = score + floor - mod
                frac = frac + (ratio / (i + 1))
            else
                score = score - ((value + mod) // 3)
                frac = frac + ((value / 5) - (floor / 7))
            end
        end

        assert(math.type(score) == "integer" and math.type(frac) == "float")
        return score, frac, score // 3, frac / #values
    end

    local a, b, c, d = analyze({ 5, 8, 13, 21, 34 })
    assert(a == 86 and c == 28)
    assert(math.abs(b - 2717 / 140) < 1e-12 and math.abs(d - 2717 / 700) < 1e-12)
    print("lua53_01#3", a, b, c, d)
    a, b, c, d = analyze({})
    assert(a == 0 and b == 0 and c == 0 and d ~= d)
    assert(select("#", analyze({})) == 4)
end

-- lua53_01#4: 方法表位运算
local function test_method_bitwise()
    local obj = {
        seed = 0x2A,
        rows = {
            { 4, 7, 9 },
            { 3, 12, 5 },
        },
    }

    function obj:fold(row_index, step)
        local row = self.rows[row_index]
        local total = self.seed ~ row_index

        for i = 1, #row do
            local base = row[i]
            local mixed = ((base << step) | (self.seed >> (i - 1))) ~ (row_index * i)

            if (mixed & 0x03) == 0 then
                total = total + (mixed // (i + 1))
            else
                total = total + (mixed % (i + 3))
            end
        end

        self.rows[row_index][#row + 1] = total & 0xFF
        return self.rows[row_index][#row], self.rows[row_index][1] ~ total
    end

    local x1, y1 = obj:fold(1, 2)
    local x2, y2 = obj:fold(2, 1)
    assert(x1 == 50 and y1 == 54 and x2 == 65 and y2 == 66)
    assert(#obj.rows[1] == 4 and #obj.rows[2] == 4)
    assert(obj.rows[1][4] == x1 and obj.rows[2][4] == x2)

    print("lua53_01#4", x1, y1, x2, y2, obj.rows[1][4], obj.rows[2][4])
end

-- lua53_01#5: 整数浮点捕获
local function test_int_float_capture()
    local function factory(seed)
        local base_int = seed * 9 + 7
        local base_float = seed / 3 + 0.625

        return function(delta)
            local left = (base_int + delta * 5) // 4
            local right = ((base_int << 1) ~ delta) & 0x7F
            local wave = base_float + delta / 8

            if (right & 0x01) == 1 then
                base_int = (base_int ~ right) + left
                base_float = wave / 2.5
            else
                base_int = (base_int | right) - left
                base_float = wave * 1.75
            end

            assert(math.type(base_int) == "integer" and math.type(base_float) == "float")
            return base_int, base_float, right // 3, wave
        end
    end

    local f = factory(11)
    local a, b, c, d, extra = f(3)
    assert(a == 91 and c == 29 and extra == nil)
    assert(math.abs(b - 28 / 15) < 1e-12 and math.abs(d - 14 / 3) < 1e-12)
    print("lua53_01#5", a, b, c, d)
    a, b, c, d, extra = f(8)
    assert(a == 95 and c == 20 and extra == nil)
    assert(math.abs(b - 301 / 60) < 1e-12 and math.abs(d - 43 / 15) < 1e-12)
    print("lua53_01#5", a, b, c, d)
    a, b, c, d, extra = f(5)
    assert(a == 130 and c == 19 and extra == nil)
    assert(math.abs(b - 677 / 300) < 1e-12 and math.abs(d - 677 / 120) < 1e-12)
    print("lua53_01#5", a, b, c, d)
end

-- lua53_01#6: 循环位运算分发
local function test_loop_dispatch(values)
    local handlers = {
        [0] = function(state, value)
            return ((state << 1) ~ value) & 0xFF
        end,
        [1] = function(state, value)
            return ((state >> 1) | (value << 2)) ~ 0x33
        end,
        [2] = function(state, value)
            return state + ((value * 5) // 2) - (value % 3)
        end,
    }

    local state = 0x41
    local log = {}
    local i = 1

    while i <= #values do
        local value = values[i]
        local kind = (value ~ i) & 0x03
        local handler = handlers[kind] or handlers[2]

        state = handler(state, value)

        if (state & 0x07) == 0 then
            log[#log + 1] = state // (i + 1)
        else
            log[#log + 1] = (state % 17) + (value / 4)
        end

        if state > 180 and i < #values then
            values[#values + 1] = ((state >> 2) ~ value) & 0x1F
        end

        i = i + 1
    end

    assert(i == #values + 1 and #log == #values)
    if values[1] == 60 then
        assert(#values > 6)
    else
        assert(state == 36 and #values == 6 and log[1] == 40 and log[3] == 10 and log[#log] == 2.5)
    end
    print("lua53_01#6", state, log[1], log[3], log[#log], #values)
end

-- lua53_01#7: 位非掩码管线
local function test_bnot_mask()
    local function make_filter(seed)
        local state = (~seed) & 0xFF

        return function(values)
            local total = 0

            for i = 1, #values do
                local flipped = (~values[i]) & 0xFF

                if (flipped & 0x03) == 0 then
                    state = ((state << 1) ~ flipped) & 0xFF
                else
                    state = ((state >> 1) | flipped) ~ i
                end

                total = total + (state // (i + 1))
            end

            return state, total, (~state) & 0xFF
        end
    end

    local f = make_filter(0x2D)
    local a, b, c, extra = f({ 3, 8, 12, 19 })
    assert(a == 20 and b == 195 and c == 235 and extra == nil)
    print("lua53_01#7", a, b, c)
    a, b, c, extra = f({ 5, 7, 11 })
    assert(a == 232 and b == 187 and c == 23 and extra == nil)
    print("lua53_01#7", a, b, c)
end

test_bitwise_idiv()
test_closure_mesh()
test_idiv_float()
test_method_bitwise()
test_int_float_capture()
test_loop_dispatch({ 6, 11, 4, 15, 9, 2 })
test_loop_dispatch({ 60, 11, 4, 15, 9, 2 })
test_bnot_mask()
