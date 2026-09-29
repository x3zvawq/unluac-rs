-- regress_412_method_chain_callback_root: method-chain sugar must keep a call-result root across an opaque callback
-- unluac: expect-not-contains [[:make():finish()]]
-- unluac: expect-ast-count [[local-binding]] [[9]]
-- unluac: expect-ast-count [[function]] [[3]]
-- unluac: expect-ast-count [[repeat]] [[1]]

local weak_values = setmetatable({}, { __mode = "v" })
local provider = {}
local makes, finishes, observations = 0, 0, 0

function provider:make()
    makes = makes + 1
    local value = {
        finish = function() finishes = finishes + 1 end,
    }
    weak_values.value = value
    return value
end

local function observe()
    collectgarbage("restart")
    collectgarbage("collect")
    collectgarbage("collect")
    assert(weak_values.value ~= nil, "call result collected before local scope ended")
    observations = observations + 1
    return observations >= 3
end

collectgarbage("stop")
local value = provider:make()
value:finish()
observe()

repeat
    local repeat_value = provider:make()
    repeat_value:finish()
until observe()
assert(makes == 3 and finishes == 3 and observations == 3)
value = nil
collectgarbage("collect")
collectgarbage("collect")
assert(weak_values.value == nil)

print("regress_412_method_chain_callback_root", "OK")
