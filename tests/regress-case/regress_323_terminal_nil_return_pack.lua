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
print("regress_323_terminal_nil_return_pack", value, index)
