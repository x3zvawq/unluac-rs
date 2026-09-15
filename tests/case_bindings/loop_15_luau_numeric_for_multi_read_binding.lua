-- regress_302_luau_numeric_for_multi_read_binding: 同一header phi的多次读取直接复用for local
-- unluac: expect-contains [[r1_1 = r1_1 + r1_2 + r1_2]]
-- unluac: expect-not-contains [[0 + 1 + 1 + 2 + 2 + 3 + 3]]
-- unluac: expect-not-contains [[local r1_3 = r1_2]]
-- unluac: expect-not-contains [[unresolved]]
-- unluac: expect-not-contains [[unluac error]]
local function sum_twice(limit)
    local function opaque(value)
        return value
    end

    local total = 0
    for index = 1, limit do
        total += opaque(index)
        total += opaque(index)
    end
    return total
end

local function terminal_capture(limit)
    for index = 1, limit do
        return function()
            return index
        end
    end
end

local continued = {}
for index = 1, 2 do
    continued[#continued + 1] = function()
        return index
    end
    continue
end

local sum = sum_twice(3)
local terminal = terminal_capture(1)()
local first = continued[1]()
local second = continued[2]()
assert(sum == 12 and terminal == 1 and first == 1 and second == 2)
print(
    "regress_302_luau_numeric_for_multi_read_binding",
    sum, terminal, first, second
)
