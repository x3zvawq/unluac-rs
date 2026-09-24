-- 内联参数在高槽求值，pack 的单结果经 GETTABLEN 写回低槽；不能增加真实 CALL。
-- unluac: expect-ast-count [[local-decl]] [[0]] [[@proto=1]]
-- unluac: expect-ast-count [[empty-local]] [[0]]
-- unluac: expect-contains [[local result = select_table({ value = false })]] [[@debug=retained]]
-- unluac: expect-contains [[local selected = select_table({ value = chosen })]] [[@debug=retained]]
-- unluac: expect-contains [[local empty = select_table({})]] [[@debug=retained]]
-- unluac: expect-contains [[--!optimize 2]] [[@variant=O2]]
-- 在独立 observer 中替换库函数，避免 getfenv/setfenv 禁止被测模块的 O2 内联。
-- 输出调用者签名，原编译器是否内联决定预期；额外真实 CALL 不能仅凭返回值相同通过。
-- unluac-runtime: local run = ...
-- unluac-runtime: local weak = setmetatable({}, { __mode = "v" })
-- unluac-runtime: local freezes, packs = 0, 0
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
-- unluac-runtime:         collectgarbage("collect")
-- unluac-runtime:         print("pack-root", weak[1] ~= nil)
-- unluac-runtime:         return table.isfrozen(value)
-- unluac-runtime:     end,
-- unluac-runtime: }
-- unluac-runtime: setfenv(run, setmetatable({ table = library }, { __index = getfenv() }))
-- unluac-runtime: run()
-- unluac-runtime: assert(freezes == 3 and packs == 3)
local function select_table(source)
    return table.pack(table.freeze(source.value or {}))[1]
end
local result = select_table({ value = false })
assert(table.isfrozen(result))
assert(next(result) == nil)
local chosen = {}
local selected = select_table({ value = chosen })
assert(selected == chosen)
assert(table.isfrozen(selected))
local empty = select_table({})
assert(empty ~= result)
assert(table.isfrozen(empty))
assert(next(empty) == nil)
print("expanded-indexed-result", true)
