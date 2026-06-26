-- regress_38_method_chain_live_receiver#1: method-chain sugar 不能删掉后续仍活跃的 receiver local
-- unluac: expect-not-contains [[unluac error]]
-- unluac: expect-contains [[getLayoutPosition()]]

local function make_child(name)
    return {
        name = name,
        visible = false,
        w = 5,
        x = 0,
        y = 0,
        setVisible = function(self, value)
            self.visible = value
        end,
        getLayoutPosition = function(self)
            return 10, 20
        end,
        setPosition = function(self, x, y)
            self.x = x
            self.y = y
        end,
    }
end

local function sample(root)
    local button = root:getChild("button")
    button:setVisible(true)
    local x, y = button:getLayoutPosition()
    local target_x = x + button.w
    local done = function()
        return button.x
    end
    button:setPosition(target_x, y)
    return button.visible, done(), button.y
end

local root = {
    getChild = function(self, name)
        return make_child(name)
    end,
}

local visible, x, y = sample(root)
print("regress_38_method_chain_live_receiver#1", visible, x, y)
