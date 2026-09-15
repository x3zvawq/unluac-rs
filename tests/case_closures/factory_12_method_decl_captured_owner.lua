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

-- 捕获的 obj 与调用接收者故意不同，避免两者被错误合并仍能通过测试。
local owner = { value = "owner" }
local receiver = { value = "receiver" }
local parent = {}
local log = {}
function owner:getLoc()
    assert(self == owner)
    log[#log + 1] = "get"
    return 7, 11
end
function receiver:setLoc(x, y)
    assert(self == receiver and x == 0 and y == 0)
    log[#log + 1] = "loc"
end
function receiver:setParent(value)
    assert(self == receiver and value == parent)
    log[#log + 1] = "parent"
end
assert(install(owner) == owner)
local x, y = owner.init(receiver, parent)
assert(x == 7 and y == 11 and table.concat(log, ",") == "get,loc,parent")
assert(owner.read(receiver) == "receiver" and owner.read(owner) == "owner")
print("regress_65#1", x, y, table.concat(log, ","), owner.read(receiver))
