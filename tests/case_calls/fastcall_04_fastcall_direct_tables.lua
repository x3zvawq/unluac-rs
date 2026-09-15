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

-- 查表真值保留原对象，false/nil 才分配备用表；嵌套调用不能提前固定 callee。
-- unluac: expect-ast-count [[local-decl]] [[0]] [[@proto=2]] [[@debug=stripped]] [[@variant=O1]]
local function select_table(source)
    return table.pack(table.freeze(source.value or {}))[1]
end
local chosen = {}
assert(select_table({ value = chosen }) == chosen and table.isfrozen(chosen))
local false_result = select_table({ value = false })
local nil_result = select_table({})
assert(false_result ~= nil_result and table.isfrozen(false_result) and table.isfrozen(nil_result))
assert(next(false_result) == nil and next(nil_result) == nil)
local lookups = 0
local supplied = {}
local proxy = setmetatable({}, { __index = function(_, key)
    assert(key == "value")
    lookups += 1
    return supplied
end })
assert(select_table(proxy) == supplied and lookups == 1 and table.isfrozen(supplied))
print("fastcall-conditional-table", true)
