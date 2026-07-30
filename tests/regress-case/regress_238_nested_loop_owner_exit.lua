-- regress_238_nested_loop_owner_exit: nested owner preserves the outer normal exit
-- unluac: expect-not-contains [[unluac error]]
-- unluac: expect-not-contains [[unresolved]]
-- unluac: expect-contains [[goto L0]]
-- unluac: expect-contains [[break]]
local restarted = false

local function iter(_, control)
    if control < 2 then
        return control + 1
    end
end

::restart::
for value in iter, nil, 0 do
    if value == 1 and not restarted then
        restarted = true
        goto restart
    end
end

print("regress_238_nested_loop_owner_exit", restarted)
