-- regress_228_generic_for_cleanup_shared_continuation#1: generic-for Close pad 归一到共享 continuation
-- unluac: expect-not-contains [[goto ]]
-- unluac: expect-not-contains [[::L]]
-- unluac: expect-not-contains [[unluac error]]
local function run(a, b, c, items, value, fallback)
    if (a or b) and c ~= nil then
        for _ in items do
            if value ~= nil then
                return value
            end
        end
    end
    if fallback then
        return fallback
    end
    return 0
end

local function once(_, control)
    if control == nil then
        return 1
    end
end

print(run(true, false, true, once, 7, false), run(false, false, true, once, 7, 9))
