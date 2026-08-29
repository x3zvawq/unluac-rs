-- regress_355_mechanical_return_root_lifetime: nested return uses do not take over a recovered root

local weak_values = setmetatable({}, { __mode = "v" })
local methods = setmetatable({}, { __mode = "k" })
local owner = {}
weak_values.key = owner
methods[owner] = function(alive)
    return alive
end

local function probe_gc()
    collectgarbage("restart")
    collectgarbage("collect")
    collectgarbage("collect")
    return weak_values.key ~= nil
end

local function check(lhs, rhs, weak_entries, method_entries)
    local marker = lhs + rhs
    local key = weak_entries.key
    return marker, method_entries[key](probe_gc())
end

collectgarbage("stop")
owner = nil
local marker, alive = check(20, 22, weak_values, methods)
assert(marker == 42 and alive)
