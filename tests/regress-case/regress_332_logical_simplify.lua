-- regress_332_logical_simplify: occurrence 级逻辑化简保留求值轨迹、标量宽度与 Luau number 语义
-- unluac: expect-contains [[return p2_0 and (p2_1 or]]
-- unluac: expect-contains [[p6_0 and r6_0() or p6_0 and r6_1()]]

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
