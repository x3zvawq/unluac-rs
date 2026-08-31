-- regress_336_loop_branch_state_copy: branch state 恢复必须证明所有回边及可重入写后的入口关系
-- unluac: expect-not-contains [[unluac error]]

local handler = {}

function handler:getCurrentMode()
    return "mode", { name = "current" }, { { name = "other" } }
end

local function while_case()
    local _, current, modes = handler:getCurrentMode()
    local selected = current
    selected.name = selected.name
    local round = 0
    while round < 2 do
        round = round + 1
        if round == 1 then
            selected = modes[1]
        else
            selected = current
        end
    end
    return selected.name
end

local function repeat_case()
    local _, current, modes = handler:getCurrentMode()
    local selected = current
    selected.name = selected.name
    local round = 0
    repeat
        round = round + 1
        if round == 1 then
            selected = modes[1]
        else
            selected = current
        end
    until round == 2
    return selected.name
end

local function numeric_for_case()
    local _, current, modes = handler:getCurrentMode()
    local selected = current
    for round = 1, 2 do
        if round == 1 then
            selected = modes[1]
        else
            selected = current
        end
    end
    return selected.name
end

local function generic_for_case()
    local _, current, modes = handler:getCurrentMode()
    local selected = current
    for _, round in ipairs({ 1, 2 }) do
        if round == 1 then
            selected = modes[1]
        else
            selected = current
        end
    end
    return selected.name
end

local function capture_case(restore)
    local _, current, modes = handler:getCurrentMode()
    local selected = current
    local function mutate()
        selected = modes[1]
    end
    mutate()
    if restore then
        selected = current
    else
        selected = modes[1]
    end
    return selected.name
end

assert(while_case() == "current")
assert(repeat_case() == "current")
assert(numeric_for_case() == "current")
assert(generic_for_case() == "current")
assert(capture_case(true) == "current")

print(
    "regress_336_loop_branch_state_copy",
    while_case(),
    repeat_case(),
    numeric_for_case(),
    generic_for_case(),
    capture_case(true)
)
