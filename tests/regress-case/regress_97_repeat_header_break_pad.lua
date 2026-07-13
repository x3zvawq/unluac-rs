-- regress_97_repeat_header_break_pad#1: a repeat body break pad must not become the loop post block
-- unluac: expect-contains [[while ]]
-- unluac: expect-contains [[repeat]]
-- unluac: expect-contains [[until ]]
-- unluac: expect-not-contains [[goto ]]
-- unluac: expect-not-contains [[::L]]
-- unluac: expect-not-contains [[unresolved]]
-- unluac: expect-not-contains [[unluac error]]
local function run(a, b, c)
    local x = 0
    while not b do
        repeat
            if a or c then
                if a and b then
                    break
                end
                break
            else
                x = x + 1
            end
        until b
    end
    return x
end

print("regress_97_repeat_header_break_pad#1", run(false, true, false))
