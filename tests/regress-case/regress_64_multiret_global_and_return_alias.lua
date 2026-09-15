-- unluac: expect-not-contains [[xmin, ymin, xmax, ymax =]]
-- unluac: expect-not-contains [[local r1_0 = p1_0]]
-- The branch-carried x/y locals occupy the first two recovered identities. The fixed
-- call results therefore start at r1_2; the assertion is about the initializer merge,
-- not about reclaiming those earlier identities.
-- unluac: expect-contains [[local r1_2, r1_3, r1_4, r1_5 = p1_0:getAdjustedRect()]]
-- unluac: expect-contains [[ymax = r1_5]]
-- unluac: expect-contains [[xmin = r1_2]]
-- unluac: expect-contains [[local r2_4 = math.abs(r2_2 - r2_0)]]
-- 保留原 height 初始化与 CALL 槽；不强制把它改成返回参数区里的新调用。
-- unluac: expect-contains [[local r2_5 = math.abs(r2_3 - r2_1)]]
-- unluac: expect-contains [[return r2_4, r2_5]]
-- unluac: expect-not-contains [[unluac error]]

local function circle(self, x, y, radius)
    if not (x and y and radius) then
        xmin, ymin, xmax, ymax = self:getAdjustedRect()
        x = (xmin + xmax) / 2
        y = (ymin + ymax) / 2
        radius = math.min((xmax - xmin) / 2, (ymax - ymin) / 2)
    end
    return x, y, radius
end

local function size(self)
    local xmin, ymin, xmax, ymax = self:getAdjustedRect()
    if xmin == nil or ymin == nil or xmax == 0 or ymax == 0 then
        return 0, 0
    end
    local width = math.abs(xmax - xmin)
    local height = math.abs(ymax - ymin)
    return width, height
end

local calls = 0
local bounds = { 2, 4, 10, 16 }
local owner = {}
function owner:getAdjustedRect()
    assert(self == owner)
    calls = calls + 1
    return unpack(bounds, 1, 4)
end
local x, y, r = circle(owner, 0, 0, 0)
assert(x == 0 and y == 0 and r == 0 and calls == 0)
x, y, r = circle(owner, nil, 1, 2)
assert(x == 6 and y == 10 and r == 4 and calls == 1)
assert(xmin == 2 and ymin == 4 and xmax == 10 and ymax == 16)
local w, h = size(owner)
assert(w == 8 and h == 12 and calls == 2)
bounds = { 10, 16, 2, 4 }
w, h = size(owner)
assert(w == 8 and h == 12 and calls == 3)
for invalid = 1, 4 do
    bounds = { 2, 4, 10, 16 }
    if invalid <= 2 then bounds[invalid] = nil else bounds[invalid] = 0 end
    w, h = size(owner)
    assert(w == 0 and h == 0 and calls == 3 + invalid)
end
print("regress_64#1", x, y, r, xmin, ymin, xmax, ymax, calls)
