-- regress_308_debug_names_all_dialects#1: 所有 naming mode 都应优先使用跨方言 debug binding
-- unluac: expect-contains [[local debug_values =]]
-- unluac: expect-contains [[local function debug_sum(debug_limit)]]
-- unluac: expect-contains [[local debug_total = 0]]
-- unluac: expect-contains [[for debug_index = 1, debug_limit do]]
-- unluac: expect-contains [[for debug_key, debug_value in ipairs(debug_values) do]]
-- unluac: expect-contains [[local function debug_nested()]]
-- unluac: expect-not-contains [[goto ]]
-- unluac: expect-not-contains [[unluac error]]
local debug_values = { 1, 2, 3 }

local function debug_sum(debug_limit)
    local debug_total = 0
    for debug_index = 1, debug_limit do
        debug_total = debug_total + debug_index
    end
    for debug_key, debug_value in ipairs(debug_values) do
        debug_total = debug_total + debug_key + debug_value
    end

    local function debug_nested()
        return debug_total
    end

    return debug_nested()
end

print("regress_308_debug_names_all_dialects#1", debug_sum(3))
