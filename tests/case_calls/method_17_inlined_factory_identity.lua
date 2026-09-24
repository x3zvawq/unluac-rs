-- 同形工厂不能混同闭包身份；捕获更新须在原 NAMECALL 顺序中求值一次。
-- unluac: expect-ast-count [[method-call]] [[2]] [[@proto=0]]
-- unluac: expect-ast-count [[local-binding]] [[6]] [[@proto=0]]
-- unluac: expect-ast-count [[assign]] [[2]] [[@proto=0]]

local sum = 0
local function mark(value)
    sum = sum + value
    return value
end
local function first()
    local object = { total = 0 }
    function object:step(value)
        self.total = self.total + value
        return self
    end
    return object
end
local function second()
    local object = { total = 0 }
    function object:step(value)
        self.total = self.total + value
        return self
    end
    return object
end
local object = first()
object = object:step(mark(3))
local other = second()
other = other:step(mark(5))
assert(object.step ~= other.step)
assert(object.total == 3)
assert(other.total == 5)
assert(sum == 8)
print("factory-identity", "OK")
