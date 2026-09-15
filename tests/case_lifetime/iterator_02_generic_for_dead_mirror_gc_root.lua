-- regress_347_generic_for_dead_mirror_gc_root: dead generic-for carrier local must not keep the
-- previous binding alive across a weak-value GC observation.
-- unluac: expect-contains [[for ]]
-- unluac: expect-contains [[while ]]
-- unluac: expect-not-contains [[unluac error]]
local function iter_once()
    local done = false
    return function()
        if done then
            return nil
        end
        done = true
        return 1, {}
    end, nil, nil
end

local function run()
    for _, value in iter_once() do
        local weak = setmetatable({}, { __mode = "v" })
        local steps = 1
        while steps > 0 do
            weak[1] = value
            value = {}
            collectgarbage("collect")
            steps = steps - 1
        end
        return weak[1] ~= nil
    end
    return false
end

local kept = run()
assert(kept == false)
print("regress_347_generic_for_dead_mirror_gc_root", kept)
