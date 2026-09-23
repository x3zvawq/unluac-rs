-- 全 direct 与 mixed 参数使用同一 FASTCALL 准备顺序，保留表身份与字段调用次序。
-- unluac: expect-ast-count [[empty-local]] [[0]] [[@variant=O1]]
-- unluac: expect-ast-count [[table-list-field]] [[1]] [[@proto=0]]
-- unluac: expect-contains [[assert(weak[1] == object and getmetatable(weak).__mode == "v")]] [[@debug=retained]]
-- unluac: expect-contains [[local meta = { __index = { value = 11 } }]] [[@debug=retained]]
-- unluac: expect-contains [[math.max(calls[1]("a", 2), calls[1]("b", 3))]] [[@debug=retained]]
-- unluac-runtime: local run = ...
-- unluac-runtime: local weak = setmetatable({}, { __mode = "v" })
-- unluac-runtime: local freezes, packs, queries = 0, 0, 0
-- unluac-runtime: local library = {
-- unluac-runtime:     freeze = function(value)
-- unluac-runtime:         freezes += 1
-- unluac-runtime:         local params, vararg = debug.info(2, "a")
-- unluac-runtime:         print("freeze-caller", params, vararg)
-- unluac-runtime:         return table.freeze(value)
-- unluac-runtime:     end,
-- unluac-runtime:     pack = function(...)
-- unluac-runtime:         packs += 1
-- unluac-runtime:         assert(select("#", ...) == 1)
-- unluac-runtime:         local result = table.pack(...)
-- unluac-runtime:         weak[1] = result
-- unluac-runtime:         return result
-- unluac-runtime:     end,
-- unluac-runtime:     isfrozen = function(value)
-- unluac-runtime:         queries += 1
-- unluac-runtime:         collectgarbage("collect")
-- unluac-runtime:         print("pack-root", weak[1] ~= nil)
-- unluac-runtime:         return table.isfrozen(value)
-- unluac-runtime:     end,
-- unluac-runtime: }
-- unluac-runtime: setfenv(run, setmetatable({ table = library }, { __index = getfenv() }))
-- unluac-runtime: run()
-- unluac-runtime: assert(freezes == 5 and packs == 4 and queries == 5)
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
-- unluac: expect-ast-count [[local-decl]] [[0]] [[@proto=2]]
-- unluac: expect-contains [[assert(select_table({ value = chosen }) == chosen and table.isfrozen(chosen))]] [[@debug=retained]]
-- unluac: expect-contains [[local false_result = select_table({ value = false })]] [[@debug=retained]]
-- unluac: expect-contains [[local nil_result = select_table({})]] [[@debug=retained]]
-- unluac: expect-contains [[local proxy = setmetatable({}, {]] [[@debug=retained]]
-- unluac: expect-contains [[--!optimize 2]] [[@variant=O2]]
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
