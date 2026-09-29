-- CALL 读取已声明的低槽，再将真假值写回该槽；不能提前初始化或保留机械结果交接。
-- unluac: expect-ast-count [[local-binding]] [[1]] [[@proto=1]]
-- unluac: expect-ast-count [[call]] [[1]] [[@proto=1]]
-- unluac: expect-ast-count [[if]] [[1]] [[@proto=1]]
-- unluac: expect-ast-count [[function]] [[2]]
-- unluac: expect-ast-max [[local-binding]] [[3]]
local calls = 0
local function evaluate(input)
    local result
    if (function()
        calls = calls + 1
        assert(result == nil)
        return input
    end)() then
        result = true
    else
        result = false
    end
    return result
end

assert(evaluate(nil) == false)
assert(evaluate(false) == false)
assert(evaluate(true) == true)
assert(evaluate(0) == true)
assert(evaluate("") == true)
assert(evaluate({}) == true)
assert(calls == 6)
print("call-truthiness-writeback", calls)
assert(evaluate(false) == false)
assert(select("#", evaluate(nil)) == 1)
assert(select("#", evaluate("again")) == 1)
assert(calls == 9)
