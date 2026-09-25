-- 完整短路条件已接管提前出口时，入口定义仍属于外层，不能困在合成 repeat 中。
-- unluac: expect-not-contains [[repeat]]
-- unluac: expect-not-contains [[goto ]]
-- unluac: expect-ast-count [[if]] [[1]]
-- unluac: expect-ast-count [[local-binding]] [[3]]
-- unluac: expect-contains [[:add("button")]]

local state = {
    enabled = false,
    mattel = nil,
    powerups = true,
    purchased = true,
    count = 0,
}
function state:add(name)
    assert(name == "button")
    self.count = self.count + 1
end

local enabled = state.enabled
if not enabled then
    if state.mattel and state.mattel.active then
    elseif state.powerups then
        if not state.purchased and not enabled then
        else
            state:add("button")
        end
    end
end

-- 两个入口绑定在出口之后仍有读取，不能靠删除它们掩盖错误作用域。
local result = state.count
assert(result == 1 and state.count == 1 and enabled == false)
print("condition_prefix_scope", result, enabled)
