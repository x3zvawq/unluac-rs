-- regress_347_generic_for_dead_mirror_gc_root: dead generic-for carrier local must not keep the
-- previous binding alive across a weak-value GC observation.
-- unluac: expect-contains [[for ]]
-- unluac: expect-contains [[while ]]
-- unluac: expect-not-contains [[unluac error]]
-- unluac: expect-ast-count [[local-binding]] [[11]]
-- unluac: expect-ast-count [[function]] [[3]]
-- unluac: expect-ast-count [[generic-for]] [[1]]
-- unluac: expect-ast-count [[while]] [[1]]
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

local next_item = iter_once()
local index, item = next_item()
assert(index == 1 and type(item) == "table")
assert(next_item() == nil)
