-- A recovered local reassigned to a collectable value must die before a moved single-pass tail.

local weak = setmetatable({}, { __mode = "v" })

local function run(skip)
    local observed
    repeat
        if skip then
            break
        else
            local value = nil
            value = {}
            weak[1] = value
        end
        collectgarbage("collect")
        observed = weak[1] ~= nil
    until true
    return observed
end

assert(run(false) == false)

-- A call result can have different exact scalar overwrites on terminal branches.  The live
-- `true` endpoint is harmless after promotion because its suffix returns without another GC
-- observation; the dead nil endpoint must still overwrite the producer's physical-root owner.
local weak_keys = setmetatable({}, { __mode = "k" })

local function make_root()
    local value = {}
    weak_keys[value] = true
    return value
end

local function root_is_live()
    collectgarbage("collect")
    return next(weak_keys) ~= nil
end

local function root_is_dead()
    collectgarbage("collect")
    return next(weak_keys) == nil
end

local function overwrite_on_terminal_branches(enabled)
    do
        local old = make_root()
        assert(root_is_live())
    end
    if enabled then
        local cleared
        cleared = root_is_dead()
        return cleared
    end
    return true
end

assert(overwrite_on_terminal_branches(true))
print("regress_441_repeat_tail_reassigned_root", "OK")
