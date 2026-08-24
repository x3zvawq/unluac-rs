-- regress_255_header_retry_terminal_state#1: direct sibling latch 保留 header-retry state
-- unluac: expect-not-contains [[end)(]]
-- unluac: expect-contains [[for ]]
-- unluac: expect-not-contains [[goto ]]
-- unluac: expect-not-contains [[::L]]
-- unluac: expect-not-contains [[unresolved]]
-- unluac: expect-not-contains [[unluac error]]
local function run(inner, iterator)
    local done, round, count = false, 0, 0
    repeat
        repeat
            for key, value in iterator do
                count = count + key + value
            end
        until not inner
        if done and inner then break end
        round = round + 1
        done = round > 1
    until done
    return round, count
end

local function once(_, control)
    if control == nil then return 1, 1 end
end

local round, count = run(false, once)
assert(round == 2, round)
assert(count == 4, count)
print("regress_255_header_retry_terminal_state#1", round, count)
