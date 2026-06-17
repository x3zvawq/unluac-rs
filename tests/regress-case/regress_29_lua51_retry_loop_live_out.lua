-- regress_29_lua51_retry_loop_live_out#1: retry loop should keep live-out values defined inside the loop
-- unluac: expect-contains [[while true do]]
-- unluac: expect-contains [[for ]]
-- unluac: expect-not-contains [[goto ]]
-- unluac: expect-not-contains [[::L]]
-- unluac: expect-not-contains [[unluac error]]
local counts = { 3, 0, 0 }
local modes = { "red", "green", "blue" }
local current_mode = 1
local random_values = { 1, 2 }
local random_index = 0

local function next_random(_, _)
    random_index = random_index + 1
    return random_values[random_index]
end

local function randomize_mode()
    local total = 0
    for _, count in ipairs(counts) do
        total = total + count
    end

    local average = total / #modes
    local choice = current_mode
    while true do
        choice = next_random(1, #modes)
        if choice ~= current_mode and counts[choice] <= average then
            break
        end
    end

    counts[choice] = counts[choice] + 1
    print("regress_29_lua51_retry_loop_live_out#1", choice, modes[choice], counts[choice])
end

randomize_mode()
