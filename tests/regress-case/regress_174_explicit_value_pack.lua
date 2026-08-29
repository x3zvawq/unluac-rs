-- regress_174_explicit_value_pack#1: open tail 与括号截断在所有 value-list 上保持不同语义
-- unluac: expect-contains [[return "head", (]]
local function pair()
    return "a", "b"
end

local function collect(...)
    local values = { ... }
    return #values .. ":" .. table.concat(values, ",")
end

local function return_open()
    return "head", pair()
end

local function return_fixed()
    return "head", (pair())
end

local open_table = { "head", pair() }
local fixed_table = { "head", (pair()) }
local unpack_fn = table.unpack or unpack
local a, b, c = pair()
local x, y = (pair())

print(
    "regress_174_explicit_value_pack#1",
    collect("head", pair()),
    collect("head", (pair())),
    collect(return_open()),
    collect(return_fixed()),
    collect(a, b, c),
    collect(x, y),
    collect(unpack_fn(open_table)),
    collect(unpack_fn(fixed_table))
)

-- regress_174_explicit_value_pack#2: open vararg 只能由消费它的尾位置展开
local function forward(...)
    return collect("open", ...), collect("fixed", (...))
end

print("regress_174_explicit_value_pack#2", forward("x", "y"))

-- regress_174_explicit_value_pack#3: nested open producer 每层只求值一次
local calls = 0
local function counted_pair()
    calls = calls + 1
    return calls, calls + 10
end

local function wrap(...)
    return collect("wrap", ...)
end

print("regress_174_explicit_value_pack#3", wrap(counted_pair()), calls)

-- regress_174_explicit_value_pack#4: generic-for iterator 列表同样保留 open/fixed 边界
local function iterator_factory(label)
    local emitted = false
    return function()
        if emitted then
            return nil
        end
        emitted = true
        return label
    end, "state", "control"
end

local iterated = {}
for value in iterator_factory("open") do
    iterated[#iterated + 1] = value
end
for value in (iterator_factory("fixed")) do
    iterated[#iterated + 1] = value
end
print("regress_174_explicit_value_pack#4", table.concat(iterated, ","))

-- regress_174_explicit_value_pack#5: generic-for 的显式前缀不能阻断尾部 value pack
local function state_factory(label)
    return { [label] = "value" }, nil
end

local prefixed = {}
for key, value in next, state_factory("open") do
    prefixed[#prefixed + 1] = key .. ":" .. value
end
for key, value in next, (state_factory("fixed")) do
    prefixed[#prefixed + 1] = key .. ":" .. value
end
print("regress_174_explicit_value_pack#5", table.concat(prefixed, ","))

-- regress_174_explicit_value_pack#6: 终结 consumer 可以接管 UCLO 前已求值的 open pack
local function close_bridge()
    local captured = "captured"
    local function closure()
        return captured
    end
    return closure, pair()
end

local bridged, bridged_a, bridged_b = close_bridge()
print("regress_174_explicit_value_pack#6", bridged(), bridged_a, bridged_b)

-- regress_174_explicit_value_pack#7: exact vararg 在声明与重赋值中都保持目标宽度
local function exact_vararg(...)
    local first, second, third = ...
    first, second, third = ...
    return collect(first, second, third)
end

print("regress_174_explicit_value_pack#7", exact_vararg("x", "y", "z", "ignored"))

-- regress_174_explicit_value_pack#8: method receiver 不改变最终参数的 open/fixed 边界
local receiver = {}
function receiver:take(first, second)
    return collect(first, second)
end

print(
    "regress_174_explicit_value_pack#8",
    receiver:take(pair()),
    receiver:take((pair()))
)
