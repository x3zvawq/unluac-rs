-- regress_78_adjacent_loop_state_handoff#1: adjacent loops share the first loop exit state
-- unluac: expect-contains [[p1_2[r1_0] then]]
-- unluac: expect-not-contains [[goto ]]
-- unluac: expect-not-contains [[::L]]
-- unluac: expect-not-contains [[unluac error]]
local function run(a, b, xs)
    local x = 0
    for _ = 1, 3 do
        x = x + 1
    end
    repeat
        if a then
            if xs[x] then
                break
            end
            break
        elseif a and b then
            break
        end
    until a
    return x
end

print("regress_78_adjacent_loop_state_handoff#1", run(true, false, { [3] = true }))
