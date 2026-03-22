local function branch_state(values)
    local state = 0
    local out = {}

    for i = 1, #values do
        local value = values[i]

        if value > 0 then
            state = state + value
        elseif value == 0 then
            state = state + 1
        else
            state = state - value
        end

        out[#out + 1] = state
    end

    return table.concat(out, ",")
end

print("branch-state", branch_state({ 2, 0, -3, 1, -1 }))
