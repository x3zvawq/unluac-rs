-- A generic-for binding receives an unknown call result on the successful dispatch edge. Values
-- copied from that binding can remain physical roots through a repeat condition.

local weak = setmetatable({}, { __mode = "v" })
local alive_at_condition = false

local function once(value)
    local emitted = false
    return function()
        if emitted then
            return nil
        end
        emitted = true
        return value
    end
end

local function finish_iteration()
    collectgarbage("collect")
    collectgarbage("collect")
    alive_at_condition = weak[1] ~= nil
    return true
end

repeat
    local saved
    for value in once({}) do
        saved = value
    end
    weak[1] = saved
until finish_iteration()

assert(alive_at_condition)
print("regress_454_generic_for_binding_repeat_root", "OK")
