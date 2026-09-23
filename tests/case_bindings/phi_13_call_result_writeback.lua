-- 原多结果 CALL 的有序写回与 Phi 合流组成一个赋值帧，不引入额外接收变量。
-- unluac: expect-ast-max [[local-binding]] [[11]]
-- unluac: expect-ast-count [[method-call]] [[1]]
-- unluac: expect-ast-count [[if]] [[1]]
local function rect(self, x, y, width, height)
    local xmin, ymin, xmax, ymax
    if x and y and width and height then
        xmin = x - width / 2
        ymin = y - height / 2
        xmax = x + width / 2
        ymax = y + height / 2
    else
        xmin, ymin, xmax, ymax = self:getAdjustedRect()
    end
    return xmin, ymin, xmax, ymax
end

local calls = 0
local owner = {}
function owner:getAdjustedRect()
    assert(self == owner)
    calls = calls + 1
    return 1, 2, 9, 12
end
local a, b, c, d = rect(owner, 10, 20, 4, 6)
assert(a == 8 and b == 17 and c == 12 and d == 23 and calls == 0)
a, b, c, d = rect(owner, 0, 0, 0, 0)
assert(a == 0 and b == 0 and c == 0 and d == 0 and calls == 0)
a, b, c, d = rect(owner, false, 20, 4, 6)
assert(a == 1 and b == 2 and c == 9 and d == 12 and calls == 1)
a, b, c, d = rect(owner, 10, false, 4, 6)
assert(a == 1 and b == 2 and c == 9 and d == 12 and calls == 2)
a, b, c, d = rect(owner, 10, 20, false, 6)
assert(a == 1 and b == 2 and c == 9 and d == 12 and calls == 3)
a, b, c, d = rect(owner, 10, 20, 4, false)
assert(a == 1 and b == 2 and c == 9 and d == 12 and calls == 4)
print("phi-call-writeback", a, b, c, d, calls)
