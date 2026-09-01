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

local short_weak_values = setmetatable({}, { __mode = "v" })
local short_owner = {}
short_weak_values.key = short_owner

local observer = {}
function observer.probe()
    collectgarbage("restart")
    collectgarbage("collect")
    collectgarbage("collect")
    return short_weak_values.key ~= nil
end

local function check_short_circuit_root(weak_entries)
    local key = weak_entries.key
    return key and observer.probe()
end

collectgarbage("stop")
short_owner = nil
assert(check_short_circuit_root(short_weak_values))

-- The right operand is consumed by the inner concat before the outer concat runs.  Its original
-- local home still roots it through that second metamethod; folding both lookups into the return
-- expression lets a recompiled chunk release it between the two calls.
local concat_keys = setmetatable({}, { __mode = "k" })
local concat_live_counts = {}
local concat_mt = {}

local function count_concat_keys()
    collectgarbage("restart")
    collectgarbage("collect")
    collectgarbage("collect")
    local count = 0
    for _ in pairs(concat_keys) do
        count = count + 1
    end
    return count
end

function concat_mt.__concat(_, _)
    concat_live_counts[#concat_live_counts + 1] = count_concat_keys()
    return ""
end

local first_value = setmetatable({}, concat_mt)
local last_value = setmetatable({}, concat_mt)
concat_keys[first_value] = true
concat_keys[last_value] = true
local concat_user = setmetatable({ first = first_value, last = last_value }, { __mode = "v" })

local function concat_name(user)
    local first = user.first
    local last = user.last
    return first .. " " .. last
end

collectgarbage("stop")
first_value = nil
last_value = nil
assert(concat_name(concat_user) == "")
assert(concat_live_counts[1] == 2 and concat_live_counts[2] == 2)
