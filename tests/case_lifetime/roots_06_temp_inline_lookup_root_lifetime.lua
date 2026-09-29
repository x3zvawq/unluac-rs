-- regress_356_temp_inline_lookup_root_lifetime: lookup snapshots remain roots after their first use
-- unluac: expect-ast-count [[local-binding]] [[5]]
-- unluac: expect-ast-count [[function]] [[0]]

local weak_values = setmetatable({}, { __mode = "v" })
local holder = { weak = weak_values }

do
    local owner = {}
    weak_values.key = owner
    assert(weak_values.key == owner)
    owner = nil

    local weak_alias = holder.weak
    local root = weak_alias.key
    assert(weak_alias == weak_values and root ~= nil)
    assigned = root
    assert(assigned == root)

    assigned = nil
    collectgarbage("collect")
    collectgarbage("collect")
    assert(weak_values.key ~= nil)

    root = nil
    collectgarbage("collect")
    collectgarbage("collect")
    assert(weak_values.key == nil)
end
