-- regress_211_temp_inline_binding_snapshot#1: binding snapshot must stay before an earlier call
-- unluac: expect-not-contains [[unluac error]]
-- unluac: expect-not-contains [[unresolved]]
local value = 1

local function mutate()
    value = 2
    return 7
end

local snapshot = value
print("regress_211_temp_inline_binding_snapshot#1", mutate(), snapshot, value)
