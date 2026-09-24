-- 开放尾参数、方法 lookup 和低槽写回保持原方言的求值顺序。
-- unluac: expect-ast-count [[method-call]] [[2]] [[@proto=0]]
-- unluac: expect-ast-count [[local-binding]] [[3]]
-- unluac: expect-ast-count [[assign]] [[2]] [[@proto=0]]

local trace = {}
local function mark(value)
    trace[#trace + 1] = "argument"
    return value, value + 10
end
local object = setmetatable({total = 0}, {__index = function(_, key)
    assert(key == "step")
    trace[#trace + 1] = "lookup"
    return function(receiver, first, second)
        trace[#trace + 1] = "dispatch"
        receiver.total = receiver.total + first + second
        return receiver
    end
end})
object = object:step(mark(1))
object = object:step(mark(2))
assert(object.total == 26)
assert(#trace == 6)
-- 原编译结果决定 lookup 与 argument 的先后；输出让运行比较观察每次事件。
print("open_tail_method", table.concat(trace, ","), object.total)
