-- regress_137_luajit_contextual_goto#1: goto 在 LuaJIT 标识符位置不是硬关键字
-- unluac: expect-contains [[goto = 7]]
-- unluac: expect-not-contains [[_ENV]]
goto = 7
assert(goto == 7)
print("regress_137_luajit_contextual_goto#1", goto)

-- 方法查询改写 receiver 绑定时，原 SELF 捕获的对象仍作为 self 传入。
local receiver
local lookups, calls = 0, 0
receiver = setmetatable({}, {__index = function(old, key)
    assert(key == "goto")
    lookups = lookups + 1
    receiver = {}
    return function(self)
        assert(self == old)
        calls = calls + 1
        return "found"
    end
end})
local function choose(expected)
    if expected == receiver:goto() then
        return true
    end
    return false
end
assert(choose("found"))
assert(lookups == 1 and calls == 1)
-- unluac: expect-ast-count [[method-call]] [[1]] [[@proto=1]]
-- unluac: expect-ast-count [[local-binding]] [[0]] [[@proto=1]]
