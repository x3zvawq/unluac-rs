-- regress_238_nested_loop_owner_exit: nested owner preserves the outer normal exit
-- unluac: expect-not-contains [[unluac error]]
-- unluac: expect-not-contains [[unresolved]]
-- unluac: expect-contains [[goto L0]]
-- unluac: expect-ast-count [[while]] [[0]]
-- unluac: expect-ast-count [[break]] [[0]]
local restarted = false
local controls, visits = {}, {}

local function iter(_, control)
    controls[#controls + 1] = control
    if control < 2 then
        return control + 1
    end
end

::restart::
for value in iter, nil, 0 do
    visits[#visits + 1] = value
    if value == 1 and not restarted then
        restarted = true
        goto restart
    end
end

assert(restarted == true)
assert(table.concat(controls, ",") == "0,0,1,2")
assert(table.concat(visits, ",") == "1,1,2")
-- unluac: expect-ast-count [[local-binding]] [[5]] [[@proto=0]]
-- unluac: expect-ast-count [[local-binding]] [[0]] [[@proto=1]]
-- unluac: expect-ast-count [[generic-for]] [[1]]
-- unluac: expect-ast-count [[goto]] [[1]]
-- unluac: expect-ast-count [[label]] [[1]]
print("regress_238_nested_loop_owner_exit", restarted)
