-- regress_399_branch_state_allocation_capture: allocation may run a finalizer that invalidates captured branch state
-- unluac: expect-not-contains [[unluac error]]

local function make()
    return "tag", {}, {}
end

local function new_victim(mt)
    return setmetatable({}, mt)
end

local function run(flag)
    local _, current, other = make()
    local selected

    collectgarbage("collect")
    collectgarbage("stop")
    local victim = new_victim({
        __gc = function()
            selected = other
        end,
    })
    victim = nil
    collectgarbage("restart")
    collectgarbage("incremental", 0, 1, 1)

    selected = current
    for _ = 1, 1000000 do
        local allocation = {}
    end

    if flag then
        selected = current
    else
        selected = other
    end
    return selected == current
end

assert(run(true))
print("regress_399_branch_state_allocation_capture", "OK")
