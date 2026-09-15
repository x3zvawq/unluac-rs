-- regress_39_method_hint_open_arg_call#1: 同一 proto 重复 SELF 后夹着多返回参数调用时不能丢 method hint
-- unluac: expect-not-contains [[unluac error]]
-- unluac: expect-contains [[:setPlayerName(]]
-- unluac: expect-not-contains [[.setPlayerName]]
-- unluac: expect-ast-count [[local-decl]] [[0]] [[@proto=2]]

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
local second_button = root:getChild("scoreBg2")
second_button:setPlayerName(pair())
assert(child.value == "TEXTS_BASIC:TEXT_SOCIAL_YOU")
print("regress_39_method_hint_open_arg_call#1", child.value)
