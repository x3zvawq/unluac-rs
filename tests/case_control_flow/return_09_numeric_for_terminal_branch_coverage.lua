-- regress_31_numeric_for_terminal_branch_coverage#1: numeric-for 体内共享 terminal return 不应让 coverage 回退到 goto
-- unluac: expect-contains [[for]]
-- unluac: expect-contains [[return]]
-- unluac: expect-not-contains [[goto]]
-- unluac: expect-not-contains [[unluac error]]
-- unluac: expect-ast-count [[numeric-for]] [[1]]
-- unluac: expect-ast-count [[local-binding]] [[11]]
-- unluac: expect-ast-count [[if]] [[5]]
local objects = {
    world = {
        first = { definition = "BIRD" },
        next = { definition = "BIRD" },
        bait = { definition = "ME_BAIT" },
    },
}

local currentBirdIndex = 0
local disabled = 0
local calls = {}

local function getNextBird(index)
    calls[#calls + 1] = index
    if index == 1 then
        return "first"
    end
    if index == 2 then
        return "next"
    end
    return "bait"
end

local function disableME()
    disabled = disabled + 1
end

local function replace_next_bird()
    for offset = 1, 7 do
        local bird = getNextBird(currentBirdIndex + offset)
        if bird ~= nil and objects.world[bird].definition ~= "ME_BAIT" then
            local next_bird = getNextBird(currentBirdIndex + offset + 1)
            if next_bird == nil or objects.world[next_bird].definition == "ME_BAIT" then
                disableME()
            else
                return next_bird
            end
        end
    end
    disableME()
    return disabled
end

local result = replace_next_bird()
assert(result == "next" and disabled == 0)
assert(table.concat(calls, ",") == "1,2")
print("regress_31_numeric_for_terminal_branch_coverage#1", result)

currentBirdIndex, disabled, calls = 1, 0, {}
assert(replace_next_bird() == 2 and disabled == 2)
assert(table.concat(calls, ",") == "2,3,3,4,5,6,7,8")
currentBirdIndex, disabled, calls = 2, 0, {}
assert(replace_next_bird() == 1 and disabled == 1)
assert(table.concat(calls, ",") == "3,4,5,6,7,8,9")

getNextBird = function(index)
    calls[#calls + 1] = index
    if index == 2 then
        return "next"
    end
end
currentBirdIndex, disabled, calls = 0, 0, {}
assert(replace_next_bird() == 2 and disabled == 2)
assert(table.concat(calls, ",") == "1,2,3,3,4,5,6,7")
currentBirdIndex, disabled, calls = 2, 0, {}
assert(replace_next_bird() == 1 and disabled == 1)
assert(table.concat(calls, ",") == "3,4,5,6,7,8,9")
