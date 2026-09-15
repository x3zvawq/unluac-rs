-- regress_356_lookup_distinct_home_lifetime: copied lookup homes remain independent GC roots

local weak_values = setmetatable({}, { __mode = "v" })
local owner = {}
weak_values.key = owner
owner = nil

local source = weak_values.key
local copy = source
collectgarbage("collect")
assert(weak_values.key ~= nil)

copy = nil
collectgarbage("collect")
assert(weak_values.key ~= nil)

source = nil
collectgarbage("collect")
assert(weak_values.key == nil)
