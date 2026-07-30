-- regress_152_luau_while_continue_break_tail#1: early continue 不抢占后续 break 与本轮 tail
-- unluac: expect-contains [[while true do]]
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

-- regress_152_luau_while_continue_break_tail#2: nested repeat 后的 continue 仍应由外层 while 持有
local nested_x = 0
while true do
    nested_x += 1
    if nested_x < 3 then
        repeat
            nested_x += 1
        until nested_x > 2
        continue
    end
    if nested_x > 5 then
        break
    end
end
print(nested_x)

-- regress_152_luau_while_continue_break_tail#3: repeat 的出口状态不能把条件 continue 提升为无条件
local function nested_continue_state()
    local state = 0
    while state <= 5 do
        state += 1
        if state < 3 then
            repeat
                state += 1
            until state > 2
            continue
        end
    end
    return state
end

print("regress_152_luau_while_continue_break_tail#3", nested_continue_state())
