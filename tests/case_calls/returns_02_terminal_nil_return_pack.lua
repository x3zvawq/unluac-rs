-- regress_323_terminal_nil_return_pack: 终态 fixed nil pack 不应留下机械 temp
-- unluac: expect-contains [[return nil, nil]]
-- unluac: expect-not-contains [[= nil, nil]]
-- unluac: expect-not-contains [[unluac error]]

local function first_positive(values)
    local index = 1
    repeat
        local value = values[index]
        if value and value > 0 then
            return value, index
        end
        index = index + 1
    until index > #values
    return nil, nil
end

local value, index = first_positive({ -2, 0 })
assert(value == nil)
assert(index == nil)

local captured_table = { -2, 0 }
local function read_captured_table()
    return captured_table[1], captured_table[2]
end
assert(read_captured_table() == -2)
assert(select(2, read_captured_table()) == 0)

print("regress_323_terminal_nil_return_pack", value, index)
