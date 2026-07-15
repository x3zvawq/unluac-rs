-- regress_190_luau_import_open_pack#1: GETIMPORT setup 不阻断末位 open 参数 owner
-- unluac: expect-contains [[table.unpack]]
-- unluac: expect-contains [[type]]
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

print(
    "regress_190_luau_import_open_pack#1",
    unpack_created(2),
    asserted_type(),
    inserted[1]
)
