-- 展开调用的比较与条件 RHS 共同属于外层参数帧；真假路径保留调用次数和临时根。
-- unluac: expect-ast-count [[if]] [[0]]
-- unluac: expect-ast-count [[empty-local]] [[0]]
-- unluac: expect-contains [[assert(select_table({ value = compared }) == compared and table.isfrozen(compared))]] [[@debug=retained]]
-- unluac: expect-contains [[select_table({ value = nested }) == nested and #nested == 0 and table.isfrozen(nested)]] [[@debug=retained]]
-- unluac: expect-contains [[--!optimize 2]] [[@variant=O2]]
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
-- unluac-runtime: assert(freezes == 3 and packs == 3 and queries == 2)
local function select_table(source)
    return table.pack(table.freeze(source.value or {}))[1]
end
local compared = {}
assert(select_table({ value = compared }) == compared and table.isfrozen(compared))
print("expanded-short-circuit", select_table({ value = false }) == compared and table.isfrozen(compared))
local nested = {}
assert(select_table({ value = nested }) == nested and #nested == 0 and table.isfrozen(nested))
