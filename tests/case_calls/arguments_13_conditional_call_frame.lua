-- 短路参数与前一次调用复用匿名结果槽；callee 查找先于条件路径，结果固定为一值。
-- unluac: expect-ast-count [[local-binding]] [[3]]
-- unluac: expect-ast-count [[local-binding]] [[0]] [[@proto=1]]
-- unluac: expect-ast-count [[if]] [[0]]
-- unluac: expect-ast-count [[function]] [[5]]
local sink = setmetatable({}, {__index = function(_, key)
    print("lookup", key)
    return function(...)
        print("consume", select("#", ...), ...)
    end
end})
local function evaluate(value)
    print("rhs")
    rawset(sink, "accept", function() error("late callee read") end)
    return value, "extra"
end
local function run(enabled, payload)
    rawset(sink, "accept", nil)
    sink.accept(rawequal(payload, payload) and not rawequal(1LL, 1LL))
    sink.accept(enabled == true and evaluate(payload))
end
run(false, 42)
run(true, false)
run(true, nil)
run(true, 0)
print("conditional-call-frame", "OK")
