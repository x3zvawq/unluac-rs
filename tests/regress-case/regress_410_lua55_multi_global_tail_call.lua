-- regress_410_lua55_multi_global_tail_call: the reverse probe releases each consumed result slot
-- unluac: expect-contains [[global first_target, second_target =]]

global<const> assert, collectgarbage, print, rawset, setmetatable, table

local weak = setmetatable({}, { __mode = "v" })

local function values()
    local first = { value = 11 }
    local second = { value = 22 }
    weak[1] = second
    return first, second
end

local writes = {}
local env = _ENV
local second_collected
setmetatable(env, {
    __newindex = function(_, name, value)
        writes[#writes + 1] = name
        if name == "first_target" then
            collectgarbage("collect")
            second_collected = weak[1] == nil
            rawset(env, name, value)
        end
    end,
})
local function declare()
    global first_target, second_target = values()
end

declare()
setmetatable(env, nil)
global first_target, second_target

assert(first_target.value == 11, first_target.value)
assert(second_target == nil, second_target)
assert(second_collected, "second result remained rooted across the first global write")
assert(table.concat(writes, ",") == "second_target,first_target")
print("regress_410_lua55_multi_global_tail_call", first_target.value, second_target == nil)
