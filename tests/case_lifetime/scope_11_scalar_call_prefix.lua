-- 低槽标量仍承担 CALL 声明前缀，局部内联不能阻塞相邻作用域和构造器的完整恢复。
-- unluac: expect-count [[= setmetatable({}, {]] [[2]]
-- unluac: expect-not-contains [[and 1 == 1]]
-- unluac: expect-ast-count [[empty-local]] [[0]]
do
    local t = {f = function() return "old" end}
    local result = t.f()
    local x = 1
    assert(result == "old" and x == 1)
    print("prefix", result == "old" and x == 1, result)
end

do
    local old_print = print
    local observed
    local function new_print(value)
        observed = value
        old_print("new", value)
    end
    local t = {
        f = function()
            print = new_print
            return "old"
        end,
    }
    local result = t.f()
    local x = 1
    print(result == "old" and x == 1)
    assert(observed == true)
    print = old_print
end

do
    local calls = 0
    local value = setmetatable({}, {
        __unm = function()
            calls = calls + 1
            return true
        end,
    })
    do
        local unused = -value
        print("single-use unary input")
    end
    assert(calls == 1)
    print("unary result retired", calls)
end

local count = 0
local value = setmetatable({}, {
    __unm = function()
        count = count + 1
        return true
    end,
})
local gets = 0
local function get()
    gets = gets + 1
    return value
end
local result = -get() and "yes" or "no"
assert(gets == 1 and count == 1 and result == "yes")
local outer, inner = true, true
if outer then
    local unused = -value
    if inner then
        print("unused result evaluated")
    end
end
assert(count == 2 and gets == 1)
print("scope_11_scalar_call_prefix", count, result)
