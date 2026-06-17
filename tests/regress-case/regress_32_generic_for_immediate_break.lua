-- regress_32_generic_for_immediate_break#1: generic-for with immediate body break should stay structured
-- unluac: expect-contains [[for ]]
-- unluac: expect-contains [[break]]
-- unluac: expect-not-contains [[goto ]]
-- unluac: expect-not-contains [[::L]]
-- unluac: expect-not-contains [[unluac error]]
local touches = {
    first = {
        x = 1,
    },
    second = {
        x = 2,
    },
}

local touch_id = nil

local function pick_first_touch()
    if touch_id == nil then
        for id, _touch in pairs(touches) do
            touch_id = id
            break
        end
    end

    return touch_id ~= nil
end

print("regress_32_generic_for_immediate_break#1", pick_first_touch())
