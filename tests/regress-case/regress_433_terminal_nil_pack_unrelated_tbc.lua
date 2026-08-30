-- regress_433_terminal_nil_pack_unrelated_tbc: 无关 TBC 不应 blanket 阻止终态 nil pack 收回
-- unluac: expect-contains [[return nil, nil]]
-- unluac: expect-not-contains [[= nil, nil]]
-- unluac: expect-not-contains [[unluac error]]

local closed = 0
local closer = {
    __close = function()
        closed = closed + 1
    end,
}

local function first_value(values)
    do
        local guard <close> = setmetatable({}, closer)
    end

    local index = 1
    repeat
        local value = values[index]
        if value ~= nil then
            return value, index
        end
        index = index + 1
    until index > #values
    return nil, nil
end

local value, index = first_value({})
assert(value == nil and index == nil)
assert(closed == 1)
print("regress_433_terminal_nil_pack_unrelated_tbc", value, index, closed)
