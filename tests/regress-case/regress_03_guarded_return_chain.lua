-- unluac: expect-not-contains [[repeat]]
-- unluac: expect-ast-min [[if]] [[2]] [[@proto=1]]
local frame = {}

function guarded_return_chain(kind, key)
    local handled, value, extra = frame.onKeyEvent()
    if not handled and kind == "PRESS" then
        if key == "ESCAPE" or key == "KEY_BACK" then
            record("cancel")
        elseif key == "RETURN" then
            record("return")
        end
    elseif handled then
        return handled, value, extra
    end
    return "BLOCK", nil, kind
end

-- 只定义全局函数不能观察分支行为；记录回调次数、动作与含 nil 的三返回值。
local calls, action, handled, value, extra = 0, nil, false, nil, nil
frame.onKeyEvent = function()
    calls = calls + 1
    return handled, value, extra
end
function record(message)
    assert(action == nil)
    action = message
end
local cases = {
    { false, "PRESS", "ESCAPE", "cancel" },
    { false, "PRESS", "KEY_BACK", "cancel" },
    { false, "PRESS", "RETURN", "return" },
    { false, "PRESS", "OTHER" },
    { false, "RELEASE", "ESCAPE" },
    { true, "PRESS", "ESCAPE" },
    { true, "RELEASE", "RETURN" },
}
for i, case in ipairs(cases) do
    handled, value, extra = case[1], nil, "extra"
    action = nil
    local a, b, c = guarded_return_chain(case[2], case[3])
    assert(calls == i and action == case[4])
    if handled then
        assert(a == true and b == nil and c == "extra")
    else
        assert(a == "BLOCK" and b == nil and c == case[2])
    end
    print("regress_03#1", i, a, b, c, action, calls)
end
