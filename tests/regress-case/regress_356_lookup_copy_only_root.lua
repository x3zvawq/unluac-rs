-- regress_356_lookup_copy_only_root: only the copied home crosses the collection fence
-- unluac: expect-not-contains [[local r0_4 = r0_3]]

local weak_values = setmetatable({}, { __mode = "v" })
local holder = { weak = weak_values }
local owner = {}
weak_values.key = owner
owner = nil

local source = holder.weak.key
local copy = source
source = nil
collectgarbage("collect")
assert(weak_values.key ~= nil)

copy = nil
collectgarbage("collect")
assert(weak_values.key == nil)
