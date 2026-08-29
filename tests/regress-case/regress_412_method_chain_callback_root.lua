-- regress_412_method_chain_callback_root: method-chain sugar must keep a call-result root across an opaque callback
-- unluac: expect-not-contains [[:make():finish()]]

local weak_values = setmetatable({}, { __mode = "v" })
local provider = {}

function provider:make()
    local value = {
        finish = function() end,
    }
    weak_values.value = value
    return value
end

local function observe()
    collectgarbage("restart")
    collectgarbage("collect")
    collectgarbage("collect")
    assert(weak_values.value ~= nil, "call result collected before local scope ended")
    return true
end

collectgarbage("stop")
local value = provider:make()
value:finish()
observe()

repeat
    local repeat_value = provider:make()
    repeat_value:finish()
until observe()

print("regress_412_method_chain_callback_root", "OK")
