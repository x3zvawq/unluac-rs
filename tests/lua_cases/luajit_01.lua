-- luajit_01#1: goto与cdata累加
local function test_goto_cdata()
    local total = 0LL
    local i = 0LL

    ::loop::
    i = i + 1LL

    if i > 10LL then
        print("luajit_01#1", tostring(total), tostring(i))
        return
    end

    if (tonumber(i) % 3) == 0 then
        total = total + i * 2LL
        goto loop
    end

    total = total + i + 5LL
    goto loop
end

-- luajit_01#2: 复数波形折叠
local function test_imaginary_wave()
    local samples = { 1i, 2i, -3i, 4i, -5i }
    local score = 0LL
    local tags = {}

    for index = 1, #samples do
        local rendered = tostring(samples[index])
        local sign = rendered:find("%-") and "neg" or "pos"
        local magnitude = tonumber((rendered:match("(%d+)i$")))

        if sign == "neg" then
            score = score - magnitude * 2LL + index
        else
            score = score + magnitude * 3LL - index
        end

        tags[#tags + 1] = rendered .. ":" .. sign
    end

    print("luajit_01#2", table.concat(tags, "|"), tostring(score))
end

-- luajit_01#3: FFI结构体goto交叉
local function test_ffi_struct()
    local ffi = require("ffi")

    ffi.cdef([[
    typedef struct {
        int id;
        double weight;
    } item_t;
    ]])

    local items = ffi.new("item_t[4]")
    local weight_sum = 0.0

    for i = 0, 3 do
        items[i].id = i + 1
        items[i].weight = (i + 1) * 1.25
        weight_sum = weight_sum + items[i].weight
    end

    local index = 0
    local checksum = 0ULL

    ::scan::
    if index >= 4 then
        print("luajit_01#3", tostring(checksum), string.format("%.2f", weight_sum))
        return
    end

    local item = items[index]
    checksum = checksum + item.id * 3ULL + index + 1ULL
    index = index + 1
    goto scan
end

-- luajit_01#4: bit库与cdata管线
local function test_bit_cdata()
    local bit = require("bit")

    local stages = { 0x21ULL, 0x34ULL, 0x55ULL, 0x89ULL, 0x144ULL }
    local acc = 0x10ULL
    local text = {}

    for i = 1, #stages do
        local mixed = bit.bxor(tonumber(acc % 0xffULL), tonumber(stages[i] % 0xffULL))

        if mixed % 2 == 0 then
            acc = acc + mixed + i
        else
            acc = acc * 2ULL - mixed
        end

        text[#text + 1] = string.format("%02x", mixed)
    end

    print("luajit_01#4", table.concat(text, ":"), tostring(acc))
end

-- luajit_01#5: 十六进制浮点分发
local function test_hexfloat()
    local coeffs = { 0x1.8p+1, 0x1.2p+0, -0x1.0p-1, 0x1.4p-2 }
    local acc = 0x1p+0
    local parts = {}

    for i = 1, #coeffs do
        acc = acc * coeffs[i] + (i / 3)
        parts[#parts + 1] = string.format("%.6f", acc)
    end

    print("luajit_01#5", table.concat(parts, ","), string.format("%.6f", acc))
end

-- luajit_01#6: 标签闭包重入
local function test_label_closure()
    local makers = {}

    for outer = 1, 4 do
        local base = outer * 2LL

        makers[#makers + 1] = function(limit)
            local value = base
            local step = 0

            ::tick::
            step = step + 1

            if step > limit then
                return tostring(value)
            end

            if (step + outer) % 2 == 0 then
                value = value + step + 1LL
                goto tick
            end

            value = value * 2LL - step
            goto tick
        end
    end

    local out = {}

    for i = 1, #makers do
        out[i] = makers[i](i + 2)
    end

    print("luajit_01#6", table.concat(out, ","))
end

-- luajit_01#7: FFI metatype计数
local function test_ffi_metatype()
    local ffi = require("ffi")

    ffi.cdef([[
    typedef struct {
        int value;
    } counter_t;
    ]])

    local counter_t = ffi.metatype("counter_t", {
        __index = {
            bump = function(self, delta)
                self.value = self.value + delta
                return self.value
            end,
        },
    })

    local state = counter_t(3)
    local acc = 1LL

    for i = 1, 5 do
        acc = acc + state:bump(i)
    end

    print("luajit_01#7", state.value, tostring(acc))
end

-- luajit_01#8: 复数分支交叉
local function test_imaginary_branch()
    local samples = { 1i, -2i, 3i, -4i, 5i }
    local index = 1
    local total = 0ULL
    local out = {}

    ::walk::
    if index > #samples then
        print("luajit_01#8", table.concat(out, ","), tostring(total))
        return
    end

    local rendered = tostring(samples[index])
    local magnitude = tonumber((rendered:match("(%d+)i$")))

    if rendered:find("%-") then
        total = total + magnitude * 2ULL + index
        out[#out + 1] = "n" .. magnitude
    else
        total = total + magnitude + 7ULL
        out[#out + 1] = "p" .. magnitude
    end

    index = index + 1
    goto walk
end

-- luajit_01#9: ULL表旋转
local function test_ull_table()
    local queue = { 7ULL, 11ULL, 19ULL, 23ULL, 31ULL }
    local acc = 5ULL

    for step = 1, 7 do
        local head = table.remove(queue, 1)

        if step % 3 == 0 then
            acc = acc + head * 2ULL
            queue[#queue + 1] = head + step
        else
            acc = acc * 2ULL - head + step
            queue[#queue + 1] = head + 1ULL
        end
    end

    local parts = {}

    for i = 1, #queue do
        parts[i] = tostring(queue[i])
    end

    print("luajit_01#9", tostring(acc), table.concat(parts, "|"))
end

-- luajit_01#10: JIT状态与十六进制浮点
local function test_jit_status()
    local jit = require("jit")

    local flags = { jit.status() }
    local scale = 0x1.0p+2
    local acc = 0x1.0p-4

    for i = 1, 8 do
        local factor = (i % 2 == 0) and 0x1.8p-1 or -0x1.4p-2
        acc = acc * scale + factor
        scale = scale + 0x1.0p-3
    end

    local text = {}

    for i = 1, math.min(#flags, 4) do
        text[i] = tostring(flags[i])
    end

    print("luajit_01#10", table.concat(text, ","), string.format("%.6f", acc))
end

test_goto_cdata()
test_imaginary_wave()
test_ffi_struct()
test_bit_cdata()
test_hexfloat()
test_label_closure()
test_ffi_metatype()
test_imaginary_branch()
test_ull_table()
test_jit_status()
