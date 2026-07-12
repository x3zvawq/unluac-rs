-- regress_73_branch_owns_nested_loop_exit_phi#1: outer branch owns the nested loop exit phi
-- unluac: expect-contains [[return r1_0 .. ":tail"]]
-- unluac: expect-not-contains [[local r1_2]]
-- unluac: expect-not-contains [[unluac error]]

local function loop_exit_phi_owner(enabled, values)
    local result = "start"
    if enabled then
        local index = 1
        while index <= #values do
            if values[index] == "stop" then
                return "early"
            end
            index = index + 1
        end
    else
        result = "disabled"
    end
    return result .. ":tail"
end

print("regress_73_branch_owns_nested_loop_exit_phi#1", loop_exit_phi_owner(true, { "next" }))
