-- regress_440_lua55_unselected_global_arm: a dead global declaration does not keep a proven constant branch shell
-- unluac: expect-not-contains [[if true then]]
-- unluac: expect-not-contains [[if false then]]
-- unluac: expect-not-contains [[global dead_value]]

global<const> assert, setmetatable, collectgarbage

local observed = 0
local weak_values = setmetatable({}, { __mode = "v" })
local function make_root()
    return {}
end
local literal = 7
local chosen = literal == 7
if chosen then
    observed = 1
else
    global dead_value = 99
    local root_copy = make_root()
    local function dead_callback()
        return observed
    end
    weak_values.value = root_copy
    collectgarbage("collect")
    assert(weak_values.value ~= nil)
    observed = 99
end

assert(observed == 1)
