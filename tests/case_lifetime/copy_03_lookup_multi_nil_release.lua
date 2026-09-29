-- regress_356_lookup_multi_nil_release: parallel nil writes release every copied lookup home
-- unluac: expect-ast-count [[local-binding]] [[5]]
-- unluac: expect-ast-count [[empty-local]] [[0]]
-- unluac: expect-ast-count [[call]] [[6]]
-- unluac: expect-count [[.weak.key]] [[1]]

local weak_values = setmetatable({}, { __mode = "v" })
local holder = { weak = weak_values }
local owner = {}
weak_values.key = owner
owner = nil

do
    local source = holder.weak.key
    local copy = source
    collectgarbage("collect")
    assert(weak_values.key ~= nil)

    source = nil
    copy = nil
end

collectgarbage("collect")
collectgarbage("collect")
assert(weak_values.key == nil)
