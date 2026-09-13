-- 全 direct 与 mixed 参数使用同一 FASTCALL 准备顺序，保留表身份与字段调用次序。
local weak = setmetatable({}, { __mode = "v" })
local object = { value = 7 }
weak[1] = object
assert(weak[1] == object and getmetatable(weak).__mode == "v")

local meta = { __index = { value = 11 } }
local inherited = setmetatable({}, meta)
assert(inherited.value == 11 and getmetatable(inherited) == meta)

local trace = ""
local function event(label, value)
    trace = trace .. label
    return value
end
local calls = { event }
local maximum = math.max(calls[1]("a", 2), calls[1]("b", 3))
local frozen = table.freeze({ value = calls[1]("c", 5) })
assert(maximum == 3 and frozen.value == 5 and table.isfrozen(frozen))
assert(trace == "abc")
print("fastcall-direct-tables", weak[1].value, inherited.value, maximum, frozen.value, trace)
