-- 首项 return COPY 不能跨过后项选择表达式中的 __lt；它会覆盖旧算术对象的残根。
-- 两种源码形状的 GC 结果不同，既不允许删除必要暂存，也不允许给直接返回添加暂存。
-- unluac: expect-ast-count [[local-binding]] [[3]] [[@proto=5]]
-- unluac: expect-ast-count [[local-binding]] [[2]] [[@proto=6]]
-- unluac: expect-ast-count [[function]] [[6]]
-- unluac: expect-ast-count [[goto]] [[0]]
-- unluac: expect-ast-count [[error]] [[0]]
local weak = setmetatable({}, {__mode = "v"})
local observed, multiplications = nil, 0
local mt = {
    __lt = function(a, b)
        if a == 0 then
            collectgarbage("collect")
            collectgarbage("collect")
            observed = weak.a ~= nil
        end
        return true
    end,
    __mul = function()
        multiplications = multiplications + 1
        local a = setmetatable({}, {
            __mod = function() return 1 end,
            __add = function() return {} end,
        })
        weak.a = a
        return a
    end,
}
local function staged(x)
    local out = 0
    if x > 10 then
        local a = x * 2
        if a % 3 == 0 then out = a else out = a + 1 end
    end
    local val = x > 0 and "positive" or "negative"
    return out, val
end
local function direct(x)
    local out = 0
    if x > 10 then
        local a = x * 2
        if a % 3 == 0 then out = a else out = a + 1 end
    end
    return out, x > 0 and "positive" or "negative"
end
local out, val = staged(setmetatable({}, mt))
assert(type(out) == "table" and val == "positive" and observed == true)
assert(multiplications == 1)
print("staged", observed)
out, val = direct(setmetatable({}, mt))
assert(type(out) == "table" and val == "positive" and observed == false)
assert(multiplications == 2)
print("direct", observed)
