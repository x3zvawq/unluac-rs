-- regress_231_repeat_refine_exit_phi_owner#1: while-true 的等价 repeat 精化应接管多 break 的下游 live-out
-- unluac: expect-not-contains [[unresolved]]
-- unluac: expect-not-contains [[unluac error]]
-- unluac: expect-not-contains [[goto ]]
local function while_breaks(a, b)
    local x = 0
    while true do
        if a then
            x = x + 1
            if x > 2 then
                break
            end
        elseif b then
            x = x + 2
            break
        else
            break
        end
    end
    return x
end

print(
    "regress_231_repeat_refine_exit_phi_owner#1",
    while_breaks(true, false),
    while_breaks(false, true),
    while_breaks(false, false)
)

-- regress_231_repeat_refine_exit_phi_owner#2: 真实 repeat 的尾条件与提前 break 共享同一个 live-out
local function repeat_breaks(a, b)
    local x = 0
    repeat
        if a then
            x = x + 1
            if x == 2 then
                break
            end
        elseif b then
            x = x + 2
            break
        else
            break
        end
    until x > 3
    return x
end

print(
    "regress_231_repeat_refine_exit_phi_owner#2",
    repeat_breaks(true, false),
    repeat_breaks(false, true),
    repeat_breaks(false, false)
)
