-- unluac: expect-not-contains [[repeat]]
-- unluac: expect-not-contains [[goto ]]
-- unluac: expect-not-contains [[::L]]
-- unluac: expect-ast-min [[if]] [[2]] [[@proto=1]]
-- unluac: expect-ast-count [[generic-for]] [[1]]
-- unluac: expect-ast-count [[local-binding]] [[15]]
-- unluac: expect-ast-count [[local-binding]] [[12]] [[@proto=0]]
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
    { 0, "PRESS", "ESCAPE" },
    { "", "RELEASE", "RETURN" },
    { nil, "PRESS", "OTHER" },
    { false, nil, "ESCAPE" },
}
-- 第一项查表必须先于三个目标写回；回调修改 value，后续 nil 写须覆盖它。
-- 若重复读取，第二次回调会看到非 nil；若延后读取，则会看到已写入的 extra。
cases[1] = setmetatable({ [2] = "PRESS", [3] = "ESCAPE", [4] = "cancel" }, {
    __index = function(_, index)
        assert(index == 1 and calls == 0 and value == nil and extra == nil)
        value = "lookup observed"
        return false
    end,
})
for i, case in ipairs(cases) do
    handled, value, extra = case[1], nil, "extra"
    assert(value == nil and extra == "extra")
    action = nil
    local a, b, c = guarded_return_chain(case[2], case[3])
    assert(calls == i and action == case[4])
    if handled then
        assert(a == handled and b == nil and c == "extra")
    else
        assert(a == "BLOCK" and b == nil and c == case[2])
    end
    print("regress_03#1", i, a, b, c, action, calls)
end
