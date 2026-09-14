-- 函数元信息覆盖每个定义入口；表达式注释不能吞掉 end、逗号或 IIFE 后缀。
-- unluac: expect-contains [[-- proto#1 params=]]
-- unluac: expect-contains [[-- proto#2 params=]]
-- unluac: expect-contains [[-- proto#3 params=]]
-- unluac: expect-contains [[-- proto#4 params=]]
-- unluac: expect-contains [[-- proto#5 params=]]
-- unluac: expect-contains [[-- proto#6 params=]]
-- unluac: expect-contains [[-- proto#7 params=]]
-- unluac: expect-contains [[-- proto#8 params=]]
-- unluac: expect-contains [[-- proto#9 params=]]
-- unluac: expect-contains [[empty = function() -- proto#]]

local f = function(value) return value + 1 end
local object = {
    step = function(value) return value * 2 end,
    empty = function() end,
    nested = function()
        local function child(value) return value + 2 end
        return child
    end,
}
function object:read(value)
    return self.step(value)
end
local function apply(callback, value)
    return callback(value)
end
local result = apply(function(value) return value - 3 end, f(7))
local immediate = (function(value) return value + 5 end)(result)
assert(object:read(immediate) == 20)
assert(object.empty() == nil)
assert(object.nested()(8) == 10)
print("function-comments", immediate)
