-- regress_410_lua55_mixed_global_rhs: a fixed call is only the suffix of this declaration
-- unluac: expect-not-contains [[global second_target, third_target =]]
-- unluac: expect-contains [[global first_target, second_target, third_target =]]
-- unluac: expect-contains [[global prefix_target, nil_target, middle_target, last_target =]]
-- unluac: expect-ast-count [[error]] [[0]]
-- unluac: expect-ast-count [[function]] [[7]]
-- unluac: expect-ast-count [[numeric-for]] [[1]]
-- unluac: expect-ast-count [[local-binding]] [[1]] [[@proto=7]]

global<const> print, assert, setmetatable, collectgarbage, rawset, pcall, table

local function pair()
    return 22, 33
end

global first_target, second_target, third_target = 11, pair()
assert(first_target == 11 and second_target == 22 and third_target == 33)
print("regress_410_lua55_mixed_global_rhs", first_target, second_target, third_target)
global fourth_target, fifth_target = 44, pair()
assert(fourth_target == 44 and fifth_target == 22)

local function observe(occupied)
    local events = {}
    local weak = setmetatable({}, { __mode = "v" })
    local env = {}
    local snapshot = "before"
    local function head()
        events[#events + 1] = "head"
        local value = { name = snapshot }
        weak[1] = value
        return value
    end
    local function tail()
        events[#events + 1] = "tail"
        snapshot = "after"
        local value = { name = "last" }
        weak[2] = value
        return "middle", value, "discarded"
    end
    setmetatable(env, {
        __index = function(_, name)
            collectgarbage("collect")
            assert(weak[1] ~= nil)
            -- 后续 probe 逐槽覆盖已经写出的尾值，前缀对象则须存活到最后一项。
            assert((weak[2] ~= nil) == (name == "last_target" or name == "middle_target"))
            events[#events + 1] = "probe:" .. name
        end,
        __newindex = function(_, name, value)
            assert((name == "prefix_target" and value == weak[1] and value.name == "before")
                or (name == "nil_target" and value == nil)
                or (name == "middle_target" and value == "middle")
                or (name == "last_target" and value == weak[2]))
            events[#events + 1] = "store:" .. name
        end,
    })
    if occupied then
        rawset(env, occupied, true)
    end
    local function initialize()
        local _ENV = env
        global prefix_target, nil_target, middle_target, last_target = head(), nil, tail()
    end
    local ok = pcall(initialize)
    assert(snapshot == "after")
    return ok, table.concat(events, ",")
end

local targets = { "last_target", "middle_target", "nil_target", "prefix_target" }
local expected = "head,tail"
for index = 1, 4 do
    local ok, events = observe(targets[index])
    assert(not ok and events == expected, events)
    expected = expected .. ",probe:" .. targets[index] .. ",store:" .. targets[index]
end
local ok, events = observe(nil)
assert(ok and events == expected, events)
print("mixed-global-order", events)
