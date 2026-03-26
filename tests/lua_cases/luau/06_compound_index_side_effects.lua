local slots = { 3, 7, 11, 13 }
local cursor: number = 0

local function next_index(): number
    cursor += 1
    return if cursor % #slots == 0 then #slots else cursor % #slots
end

for turn = 1, 6 do
    slots[next_index()] += if turn % 2 == 0 then turn * 2 else turn
end

print("luau-sidefx", cursor, table.concat(slots, ","))
