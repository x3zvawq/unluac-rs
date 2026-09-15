-- regress_235_table_constructor_eval_ownership: moved producers keep one ordered evaluation
-- unluac: expect-not-contains [[unluac error]]
-- unluac: expect-not-contains [[unresolved]]
local log = {}

local function mark(value)
    log[#log + 1] = value
    return value
end

local first = mark("first")
local second = mark("second")
local ordered = {}
ordered.x = second
ordered.y = first
assert(table.concat(log, ",") == "first,second")
assert(ordered.x == "second" and ordered.y == "first")

log = {}
local value = mark("value")
local key = mark("key")
local keyed = {}
keyed[key] = value
assert(table.concat(log, ",") == "value,key")
assert(keyed.key == "value")

log = {}
local shared = mark("shared")
local repeated = {}
repeated[shared] = shared
repeated.a = shared
assert(table.concat(log, ",") == "shared")
assert(repeated.shared == "shared" and repeated.a == "shared")

log = {}
local direct = {}
direct[mark("direct-key")] = mark("direct-value")
assert(table.concat(log, ",") == "direct-key,direct-value")
assert(direct["direct-key"] == "direct-value")

print("regress_235_table_constructor_eval_ownership", "ok")

local parent = {}
local child = {}
parent.cross_seed = child
assert(parent.cross_seed ~= nil)
