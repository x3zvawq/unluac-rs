-- regress_356_temp_inline_lookup_root_lifetime: lookup snapshots remain roots after their first use

local weak_values = setmetatable({}, { __mode = "v" })
local holder = { weak = weak_values }

do
    local owner = {}
    weak_values.key = owner
    owner = nil

    local weak_alias = holder.weak
    local root = weak_alias.key
    assigned = root
    assert(assigned ~= nil)

    assigned = nil
    collectgarbage("collect")
    collectgarbage("collect")
    assert(weak_values.key ~= nil)

    root = nil
    collectgarbage("collect")
    collectgarbage("collect")
    assert(weak_values.key == nil)
end
