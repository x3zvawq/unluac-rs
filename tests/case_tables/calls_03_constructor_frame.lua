-- callee 与后续参数各自经过 phi，不会改变原构造器属于接收 CALL 参数区的事实。
-- 必须观察接收函数已经清空形参、但调用尚未返回的窗口；仅检查后面的槽覆盖会漏报。
-- unluac: expect-not-contains [[unluac error]]
local weak = setmetatable({}, {__mode = "v"})
local function resource()
    return {}
end
local function tail()
    return {}, nil
end
local function receive(values, tag)
    weak.seed = values
    assert(type(values[1]) == "table" and type(values[2]) == "table")
    values[1], values[2] = nil, nil
    values = nil
    collectgarbage("collect")
    collectgarbage("collect")
    print("inside-conditional-receiver", type(weak.seed))
    return tag
end
local function alternate(values, tag)
    return receive(values, tag)
end
local target = setmetatable({}, {__newindex = function(_, key, value)
    collectgarbage("collect")
    collectgarbage("collect")
    print("conditional-receiver", key, value, type(weak.seed))
end})
local function build(callee_flag, argument_flag)
    local answer = (callee_flag and receive or alternate)(
        {resource(), tail()}, argument_flag and 37 or 41)
    target.state = answer
end
collectgarbage("stop")
build(false, false)
build(false, true)
build(true, false)
build(true, true)
collectgarbage("restart")
