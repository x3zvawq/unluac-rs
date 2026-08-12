-- unluac: expect-contains [[function p1_0.init(p2_0, p2_1)]]
-- unluac: expect-contains [[:getLoc()]]
-- unluac: expect-contains [[:setLoc(0, 0)]]
-- unluac: expect-not-contains [[local r2_0 = p1_0]]
-- unluac: expect-not-contains [[local r2_3 = p2_0]]
-- unluac: expect-not-contains [[local r2_4 = p2_0]]
-- unluac: expect-not-contains [[function p1_0:init(]]
-- unluac: expect-contains [[function p1_0.read(p3_0)]]
-- unluac: expect-not-contains [[unluac error]]

local function install(obj)
    obj.init = function(self, parent)
        local x, y = obj:getLoc()
        self:setLoc(0, 0)
        self:setParent(parent)
        return x, y
    end

    obj.read = function(self)
        return self.value
    end

    return obj
end

return install
