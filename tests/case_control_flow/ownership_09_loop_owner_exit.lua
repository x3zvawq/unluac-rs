-- regress_238_nested_loop_owner_exit: nested owner preserves the outer normal exit
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
print("regress_238_nested_loop_owner_exit", restarted)
