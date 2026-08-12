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

return rect
