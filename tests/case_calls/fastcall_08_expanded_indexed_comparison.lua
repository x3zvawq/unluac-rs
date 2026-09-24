-- 比较结果的 Boolean 槽低于完整调用准备；恢复调用时保留比较和原根后缀。
-- unluac: expect-ast-count [[local-decl]] [[0]] [[@proto=1]]
-- unluac: expect-ast-count [[empty-local]] [[0]]
-- unluac: expect-ast-count [[local-decl]] [[3]] [[@proto=0]]
-- unluac: expect-not-contains [[ = print]]
-- unluac: expect-contains [[local matches = select_table({ value = compared }) == compared]] [[@debug=retained]]
-- unluac: expect-contains [[local misses = select_table({ value = false }) == compared]] [[@debug=retained]]
-- unluac: expect-contains [[--!optimize 2]] [[@variant=O2]]
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
-- unluac-runtime: assert(freezes == 2 and packs == 2)
local function select_table(source)
    return table.pack(table.freeze(source.value or {}))[1]
end
local compared = {}
local matches = select_table({ value = compared }) == compared
assert(matches)
assert(table.isfrozen(compared))
local misses = select_table({ value = false }) == compared
assert(not misses)
print("expanded-indexed-comparison", matches, misses)
