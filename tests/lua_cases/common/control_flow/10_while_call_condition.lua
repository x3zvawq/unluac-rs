local items = {10, 20, 30}
local pos = 0

local function advance()
    pos = pos + 1
    return items[pos]
end

local total = 0

while advance() do
    total = total + items[pos]
end

print("while-call-cond", total)
