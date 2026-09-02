-- unluac: expect-not-contains [[xmin, ymin, xmax, ymax =]]
-- unluac: expect-not-contains [[local r1_0 = p1_0]]
-- The branch-carried x/y locals occupy the first two recovered identities. The fixed
-- call results therefore start at r1_2; the assertion is about the initializer merge,
-- not about reclaiming those earlier identities.
-- unluac: expect-contains [[local r1_2, r1_3, r1_4, r1_5 = p1_0:getAdjustedRect()]]
-- unluac: expect-contains [[ymax = r1_5]]
-- unluac: expect-contains [[xmin = r1_2]]
-- unluac: expect-contains [[local r2_4 = math.abs(r2_2 - r2_0)]]
-- unluac: expect-contains [[return r2_4, (math.abs(r2_3 - r2_1))]]
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

return circle, size
