-- regress_332_logical_simplify: occurrence 级逻辑化简保留求值轨迹、标量宽度与 Luau number 语义
-- 稳定或恒真分支也不授权合并两个原 guard 检查。
-- unluac: expect-contains [[return p2_0 and p2_1 or p2_0 and]]
-- unluac: expect-contains [[p6_0 and r6_0() or p6_0 and r6_1()]]
-- unluac: expect-contains [[return p9_0 and {} or p9_0 and]]
-- unluac: expect-contains [[("unexpected", "fallback")]]
-- unluac: expect-contains [[if not ((p11_0 or]]
-- unluac: expect-contains [[return p12_0 and p12_1 or {}]]
-- unluac: expect-contains [[return p16_0 and p16_1 and p16_2 or {}]]

local trace = {}

local function mark(name, value)
    trace[#trace + 1] = name
    return value
end

local function shared_guard_with_call(guard, first)
    return (guard and first) or (guard and mark("c", "fallback"))
end

assert(shared_guard_with_call(true, false) == "fallback")
assert(table.concat(trace, ",") == "c")
assert(shared_guard_with_call(false, false) == false)
assert(shared_guard_with_call(nil, false) == nil)
assert(shared_guard_with_call(true, "first") == "first")
assert(table.concat(trace, ",") == "c")

local function shared_vararg_with_calls(first, second, ...)
    return (... and first()) or (... and second())
end

trace = {}
local vararg_value = shared_vararg_with_calls(
    function()
        return mark("b", false)
    end,
    function()
        return mark("c", "vararg")
    end,
    true
)
assert(vararg_value == "vararg" and table.concat(trace, ",") == "b,c")

-- 参数和 local 都能被中间 closure call 改写；这里不能把两次 guard 读取合并。
local function mutable_param_guard(guard)
    trace = {}
    local function mutate()
        trace[#trace + 1] = "b"
        guard = false
        return false
    end
    local function forbidden()
        trace[#trace + 1] = "c"
        return "wrong"
    end
    local value = (guard and mutate()) or (guard and forbidden())
    return value, table.concat(trace, ",")
end

local guarded_value, guarded_trace = mutable_param_guard(true)
assert(guarded_value == false and guarded_trace == "b")

-- 首臂分配的 table 恒真，运行时不会调用 fallback；字节码仍有该调用及控制路径，
-- 不得仅凭结果真值把它们删除。
local function truthy_allocating_first_arm(guard)
    return (guard and {}) or (guard and mark("unexpected", "fallback"))
end

trace = {}
local allocated = truthy_allocating_first_arm(true)
assert(type(allocated) == "table" and #trace == 0)
assert(truthy_allocating_first_arm(false) == false)
assert(truthy_allocating_first_arm(nil) == nil)
assert(#trace == 0)

local function condition_mark()
    return mark("condition-b", true)
end

local function truthy_shared_condition_tail(guard)
    if (guard and {}) or (condition_mark() and {}) then
        return true
    end
    return false
end

trace = {}
assert(truthy_shared_condition_tail(true) and #trace == 0)
trace = {}
assert(truthy_shared_condition_tail(false) and table.concat(trace, ",") == "condition-b")

local function truthy_effectful_shared_or_tail(guard, first)
    return (guard and (first or {})) or {}
end

local shared_tail = truthy_effectful_shared_or_tail(true, false)
local other_shared_tail = truthy_effectful_shared_or_tail(false, false)
assert(type(shared_tail) == "table" and shared_tail ~= other_shared_tail)

local function count_values(...)
    return select("#", ...), ...
end

-- logical operand 中的 `...` 是标量；化简成 bare VarArg 后，final return/argument
-- 仍必须由 fixed value-pack 降成 `(...)`，不能重新展开第二个实参。
local function scalar_return(...)
    return ... and ...
end

local function scalar_argument(...)
    return count_values(... or (... and "unreachable"))
end

local return_count, return_value = count_values(scalar_return("first", "second"))
local argument_count, argument_value = scalar_argument("first", "second")
assert(return_count == 1 and return_value == "first")
assert(argument_count == 1 and argument_value == "first")

local decimal = 1.5 + 2.25
local negative_zero = -0.0 + -0.0
local rounded = 9007199254740993 + 1
local nan = 1e999 + -1e999
assert(decimal == 3.75)
assert(1 / negative_zero == -math.huge)
assert(rounded == 9007199254740992)
assert(nan ~= nan)

print(
    "regress_332_logical_simplify",
    vararg_value,
    guarded_value,
    guarded_trace,
    return_count,
    argument_count,
    decimal,
    1 / negative_zero,
    rounded,
    nan ~= nan
)

-- 三个互斥分配来源逐层汇合；共享尾仍只分配一个新对象，并保留已有值的身份。
-- 这覆盖持久来源图继续合并的路径，不依赖输出里选择了哪一条原指令作代表。
do
    local function nested_shared_allocation(first, second, value)
        return first and (second and (value or {}) or {}) or {}
    end
    local carried = {}
    assert(nested_shared_allocation(true, true, carried) == carried)
    local first = nested_shared_allocation(true, true, false)
    local second = nested_shared_allocation(true, false, carried)
    local third = nested_shared_allocation(false, true, carried)
    assert(type(first) == "table" and type(second) == "table" and type(third) == "table")
    assert(first ~= second and second ~= third and first ~= third)
end
