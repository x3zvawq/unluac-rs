-- unluac: expect-contains [[if p1_1 and p1_2 and p1_3 and p1_4 then]]
-- unluac: expect-contains [[local r1_0, r1_1, r1_2, r1_3]]
-- unluac: expect-not-contains [[local r1_4 = p1_0]]
-- unluac: expect-contains [[local r1_4, r1_5, r1_6, r1_7 = p1_0:getAdjustedRect()]]
-- unluac: expect-not-contains [[if p1_1 then]]
-- unluac: expect-not-contains [[unluac error]]

local function rect(self, x, y, width, height)
    local xmin, ymin, xmax, ymax
    if x and y and width and height then
        xmin = x - width / 2
        ymin = y - height / 2
        xmax = x + width / 2
        ymax = y + height / 2
    else
        xmin, ymin, xmax, ymax = self:getAdjustedRect()
    end
    return xmin, ymin, xmax, ymax
end

local calls = 0
local owner = {}
function owner:getAdjustedRect()
    assert(self == owner)
    calls = calls + 1
    return 1, 2, 9, 12
end
local a, b, c, d = rect(owner, 10, 20, 4, 6)
assert(a == 8 and b == 17 and c == 12 and d == 23 and calls == 0)
a, b, c, d = rect(owner, 0, 0, 0, 0)
assert(a == 0 and b == 0 and c == 0 and d == 0 and calls == 0)
for missing = 1, 4 do
    local args = { 10, 20, 4, 6 }
    args[missing] = false
    a, b, c, d = rect(owner, unpack(args))
    assert(a == 1 and b == 2 and c == 9 and d == 12 and calls == missing)
end
print("regress_63#1", a, b, c, d, calls)
