-- regress_190_luau_import_open_pack#1: GETIMPORT setup 不阻断末位 open 参数 owner
-- unluac: expect-contains [[table.unpack]]
-- unluac: expect-contains [[type]]
-- unluac: expect-not-contains [[ = table.create]]
-- unluac: expect-not-contains [[ = assert]]
-- unluac: expect-not-contains [[ = tonumber]]
-- unluac: expect-not-contains [[unresolved]]
-- unluac: expect-not-contains [[unluac error]]

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

print(
    "regress_190_luau_import_open_pack#1",
    unpack_created(2),
    asserted_type(),
    inserted[1],
    saved_fastcall_argument(),
    saved_generic_fastcall_argument()
)
