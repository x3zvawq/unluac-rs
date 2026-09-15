-- An opaque call may retain only a weak reference to its argument. The original allocation home
-- must stay live across later observation until the exact nil overwrite ends that transaction.

local weak = setmetatable({}, { __mode = "v" })

local function publish(value)
    weak[1] = value
end

local function run()
    local value = {}
    publish(value)

    collectgarbage("collect")
    collectgarbage("collect")
    assert(weak[1] ~= nil)

    value = nil
    collectgarbage("collect")
    collectgarbage("collect")
    assert(weak[1] == nil)
end

run()
print("regress_455_allocation_call_escape", "OK")
