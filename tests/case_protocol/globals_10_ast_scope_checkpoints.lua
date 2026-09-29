-- unluac: expect-ast-count [[function]] [[7]]
-- unluac: expect-ast-count [[repeat]] [[2]]
-- unluac: expect-ast-count [[repeat]] [[1]] [[@proto=0]]
-- unluac: expect-ast-count [[repeat]] [[1]] [[@proto=6]]
-- unluac: expect-ast-count [[while]] [[0]]
-- unluac: expect-ast-count [[error]] [[0]]
-- unluac: expect-contains [[global function checkpoint_recurse(]]
-- unluac: expect-contains [[:get()]]
global<const> assert, print
-- 权限检查点不要求重建冗余的只读声明或空循环，作用域由下面的读写结果观察。

global shared = 10
do
    global initializer_result = (function()
        shared = shared + 1
        return shared
    end)()
    global<const> shared
    assert(shared == 11)
    do
        global *
        inner_gate_value = shared + 1
    end
end
shared = 12
assert(shared == 12)
assert(_ENV.initializer_result == 11 and _ENV.inner_gate_value == 12)

global function checkpoint_recurse(n)
    if n == 0 then return 7 end
    return checkpoint_recurse(n - 1)
end
assert(checkpoint_recurse(3) == 7)

local held = 20
do
    local held = (function() return held + 1 end)()
    local function recurse(n)
        if n == 0 then return held end
        return recurse(n - 1)
    end
    assert(recurse(2) == 21)
end
assert(held == 20)
repeat
    global<const> type
    local condition_value = shared
until type(condition_value) == "number"

local holder = {}
function holder:get()
    return shared
end
assert(holder:get() == 12)

-- 同块条件前缀先读取本轮值，再检测类型；一次退出及回边都不能重复或跳过读取。
local function inspect_prefix(values, expected)
    global<const> assert, setmetatable, type
    local reads = 0
    local source = setmetatable({}, {
        __index = function(_, key)
            reads = reads + 1
            assert(key == "value" and reads <= expected)
            return values[reads]
        end,
    })
    repeat
        local value = source.value
    until type(value) == "number"
    assert(reads == expected)
end
inspect_prefix({ 12 }, 1)
inspect_prefix({ "wait", false, 12 }, 3)
print("ast-scope-checkpoint-boundaries", "OK")
