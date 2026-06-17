-- regress_34_short_circuit_exit_jump_pad#1: short-circuit 出口的空 jump pad 应随条件一起消费
-- unluac: expect-not-contains [[goto ]]
-- unluac: expect-not-contains [[::L]]
-- unluac: expect-not-contains [[unluac error]]

local function maybe_add_button(state)
    local enabled = state.enabled
    if not enabled then
        if state.mattel and state.mattel.active then
        elseif state.powerups then
            if not state.purchased and not enabled then
            else
                state:add("button")
            end
        end
    end
    return state.count
end

local state = {
    enabled = false,
    mattel = nil,
    powerups = true,
    purchased = true,
    count = 0,
}

function state:add(_name)
    self.count = self.count + 1
end

print("regress_34_short_circuit_exit_jump_pad#1", maybe_add_button(state))
