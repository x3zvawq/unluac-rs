-- regress_331_luau_self_value_capture: CAPTURE VAL dst must survive a later dst overwrite
-- unluac: expect-not-contains [[unluac error]]
-- unluac: expect-not-contains [[unresolved]]
local result

for binding = 1, 1 do
    local function snapshot()
        return snapshot
    end

    result = snapshot
    binding = 99
    assert(result() == result)
    print("regress_331_luau_self_value_capture#1")
end
