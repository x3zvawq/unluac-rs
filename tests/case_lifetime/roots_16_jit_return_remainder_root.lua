-- JIT 比较前加载常量只覆盖乘法槽；取模结果仍留在更高 scratch。
-- return 首项 COPY 与选择表达式合并后会更早覆盖取模残根，GC 可观察两者差异。
-- unluac: expect-ast-count [[local-binding]] [[3]] [[@proto=2]]
-- unluac: expect-ast-count [[local-binding]] [[2]] [[@proto=1]]
-- __mul 的源码身份仅在保留 debug 时要求独立 a；stripped 可以直接单值返回。
-- unluac: expect-ast-count [[local-binding]] [[17]] [[@debug=retained]]
-- unluac: expect-ast-count [[local-binding]] [[16]] [[@debug=stripped]]
-- unluac: expect-ast-count [[function]] [[6]]
-- unluac: expect-ast-count [[goto]] [[0]]
-- unluac: expect-ast-count [[error]] [[0]]
local ffi = require("ffi")
local weak = setmetatable({}, {__mode = "v"})
local observed, multiplications = nil, 0
local mt = {
    __lt = function(a, b)
        if a == 0 then
            collectgarbage("collect")
            collectgarbage("collect")
            observed = weak.remainder ~= nil
        end
        return true
    end,
    __mul = function()
        multiplications = multiplications + 1
        local a = setmetatable({}, {
            __mod = function()
                local residue = {}
                weak.remainder = residue
                return residue
            end,
            __add = function() return {} end,
        })
        return a
    end,
}
local make = ffi.metatype("struct { int tag; }", mt)
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
collectgarbage("stop")
local out, val = staged(make())
assert(type(out) == "table" and val == "positive" and observed == true)
assert(multiplications == 1)
print("staged", observed)
out, val = direct(make())
assert(type(out) == "table" and val == "positive" and observed == false)
assert(multiplications == 2)
print("direct", observed)
collectgarbage("restart")
