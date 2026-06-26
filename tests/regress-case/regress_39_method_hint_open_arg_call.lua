-- regress_39_method_hint_open_arg_call#1: SELF 后夹着多返回参数调用时不能丢 method hint
-- unluac: expect-not-contains [[unluac error]]
-- unluac: expect-contains [[:setPlayerName(]]

local function pair()
    return "TEXTS_BASIC", "TEXT_SOCIAL_YOU"
end

local child = {
    value = "",
    setPlayerName = function(self, first, second)
        self.value = first .. ":" .. second
    end,
}

local root = {
    getChild = function(self, name)
        return child
    end,
}

local button = root:getChild("scoreBg2")
button:setPlayerName(pair())
print("regress_39_method_hint_open_arg_call#1", child.value)
