-- regress_190_luau_import_open_pack#1: GETIMPORT setup 不阻断末位 open 参数 owner
-- unluac: expect-contains [[table.unpack]]
-- unluac: expect-contains [[type]]
-- unluac: expect-not-contains [[ = table.create]]
-- unluac: expect-not-contains [[ = assert]]
-- unluac: expect-not-contains [[ = tonumber]]
-- unluac: expect-not-contains [[unresolved]]
-- unluac: expect-not-contains [[unluac error]]
-- unluac: expect-ast-count [[local-decl]] [[2]] [[@proto=0]]
-- unluac: expect-ast-count [[empty-local]] [[0]] [[@proto=0]]
-- unluac: expect-ast-count [[local-decl]] [[2]] [[@proto=4]]
-- unluac: expect-ast-count [[empty-local]] [[0]] [[@proto=4]]
-- unluac-runtime: local run = ...
-- unluac-runtime: local trace = {}
-- unluac-runtime: local observed_table = table.clone(table)
-- unluac-runtime: observed_table.create = function(count, value)
-- unluac-runtime:     assert(count == 2 and value == 1)
-- unluac-runtime:     trace[#trace + 1] = "create"
-- unluac-runtime:     return table.create(count, value)
-- unluac-runtime: end
-- unluac-runtime: observed_table.unpack = function(values)
-- unluac-runtime:     assert(#values == 2 and values[1] == 1 and values[2] == 1)
-- unluac-runtime:     trace[#trace + 1] = "unpack"
-- unluac-runtime:     return table.unpack(values)
-- unluac-runtime: end
-- unluac-runtime: observed_table.pack = function(...)
-- unluac-runtime:     local values = table.pack(...)
-- unluac-runtime:     if values.n == 4 then
-- unluac-runtime:         assert(values[1] == 1 and values[2].tag == "old" and values[3] == 2 and values[4] == 3)
-- unluac-runtime:         trace[#trace + 1] = "pack"
-- unluac-runtime:         return setmetatable({}, { __index = function(_, key)
-- unluac-runtime:             assert(key == 2)
-- unluac-runtime:             trace[#trace + 1] = "index"
-- unluac-runtime:             return setmetatable({}, { __index = function(_, field)
-- unluac-runtime:                 assert(field == "tag")
-- unluac-runtime:                 trace[#trace + 1] = "tag"
-- unluac-runtime:                 return values[2].tag
-- unluac-runtime:             end })
-- unluac-runtime:         end })
-- unluac-runtime:     end
-- unluac-runtime:     assert(values.n == 2 and values[1] == 1 and values[2] == 1)
-- unluac-runtime:     trace[#trace + 1] = "collect"
-- unluac-runtime:     return values
-- unluac-runtime: end
-- unluac-runtime: setfenv(run, setmetatable({ table = observed_table }, { __index = getfenv() }))
-- unluac-runtime: run()
-- unluac-runtime: assert(table.concat(trace, ",") == "create,unpack,collect,pack,index,tag")
-- unluac-runtime: print("regress_190_luau_import_open_pack#2", table.concat(trace, ","))

local function unpack_created(count)
    return table.unpack(table.create(count, 1))
end

local function asserted_type()
    return type(assert({}))
end

local inserted = {}
table.insert(inserted, tonumber("1"))

-- FASTCALL1 搬到 fallback argument slot 的源码 local 仍是独立快照，外层 open FASTCALL 不得放宽它。
local function saved_fastcall_argument()
    local saved = {}
    return rawlen(saved)
end

-- generic FASTCALL 的参数槽虽已在 callee fallback 前物化，源码 local 仍须保留旧值身份。
local function saved_generic_fastcall_argument()
    local current = { tag = "old" }
    local saved = current
    local function replace()
        current = { tag = "new" }
        return 1
    end
    return table.pack(replace(), saved, 2, 3)[2].tag
end

-- 非末位 print 参数会收窄为单值；先观察完整返回包，才能发现尾结果丢失。
local unpacked = table.pack(unpack_created(2))
assert(unpacked.n == 2 and unpacked[1] == 1 and unpacked[2] == 1)
print(
    "regress_190_luau_import_open_pack#1",
    unpacked.n,
    unpacked[1],
    unpacked[2],
    asserted_type(),
    inserted[1],
    saved_fastcall_argument(),
    saved_generic_fastcall_argument()
)
