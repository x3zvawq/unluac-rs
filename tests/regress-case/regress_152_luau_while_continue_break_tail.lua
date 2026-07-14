-- regress_152_luau_while_continue_break_tail#1: early continue 不抢占后续 break 与本轮 tail
-- unluac: expect-contains [[while true do]]
-- unluac: expect-contains [[elseif]]
-- unluac: expect-not-contains [[goto ]]
-- unluac: expect-not-contains [[::L]]
-- unluac: expect-not-contains [[unresolved]]
-- unluac: expect-not-contains [[unluac error]]
local x = 0
while true do
    if x == 1 then
        x = 2
        continue
    end
    if x == 2 then
        x = 3
    elseif x == 4 then
        break
    end
    x += 1
end
print(x)
