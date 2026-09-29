-- regress_353_extended_index_key_lifetime: an index local roots its key across argument evaluation
-- unluac: expect-contains [[local r3_0 =]]
-- unluac: expect-contains [[local r3_1 =]]
-- unluac: expect-ast-count [[function]] [[3]]
-- unluac: expect-ast-count [[local-binding]] [[11]]
-- unluac: expect-ast-count [[local-decl]] [[2]] [[@proto=3]]
local calls = 0
local stable = { value = "prefix" }
local weak_values = setmetatable({}, { __mode = "v" })
local methods = setmetatable({}, { __mode = "k" })

local owner = {}
weak_values.key = owner
methods[owner] = function(alive)
    assert(alive == true)
    calls = calls + 1
    return alive
end

local function probe_gc()
    collectgarbage("restart")
    collectgarbage("collect")
    collectgarbage("collect")
    return weak_values.key ~= nil
end

local function unsafe(stable_values, weak_entries, method_entries)
    local first = stable_values.value
    local key = weak_entries.key
    return first, method_entries[key](probe_gc())
end

collectgarbage("stop")
owner = nil
local prefix, alive = unsafe(stable, weak_values, methods)
assert(prefix == "prefix" and alive)
assert(calls == 1)
collectgarbage("collect")
collectgarbage("collect")
assert(weak_values.key == nil and next(methods) == nil)
