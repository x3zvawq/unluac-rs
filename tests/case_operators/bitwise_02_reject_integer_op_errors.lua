-- unluac: expect-contains [[ // ]]
-- unluac: expect-contains [[ % ]]

local function reject_floor_zero()
    local numerator = 1
    local zero = 0
    local unused = numerator // zero
    if 1 == 1 then
        print("unreachable-after-floor-zero")
    else
        print(unused)
    end
end

local function reject_mod_zero()
    local numerator = 1
    local zero = 0
    local unused = numerator % zero
    if 1 == 1 then
        print("unreachable-after-mod-zero")
    else
        print(unused)
    end
end

local function reject_float_bit_not()
    local value = 1.5
    local unused = ~value
    if 1 == 1 then
        print("unreachable-after-float-bit-not")
    else
        print(unused)
    end
end

assert(not pcall(reject_floor_zero))
assert(not pcall(reject_mod_zero))
assert(not pcall(reject_float_bit_not))

-- 动态输入即使结果无读，也必须逐次执行元方法；不能借用字面量整数证明。
local events = {}
local function method(name)
    return function()
        events[#events + 1] = name
        return 17
    end
end
local value = setmetatable({}, {
    __idiv = method("floor"),
    __mod = method("mod"),
    __band = method("and"),
    __bor = method("or"),
    __bxor = method("xor"),
    __shl = method("shl"),
    __shr = method("shr"),
    __bnot = method("not"),
})
local function discard_dynamic_ops(input)
    local a = input // 3
    local b = input % 3
    local c = input & 3
    local d = input | 3
    local e = input ~ 3
    local f = input << 3
    local g = input >> 3
    local h = ~input
    if 1 == 1 then
        print("dynamic-integer-ops")
    else
        print(a, b, c, d, e, f, g, h)
    end
end
discard_dynamic_ops(value)
assert(table.concat(events, ",") == "floor,mod,and,or,xor,shl,shr,not")
