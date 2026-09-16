-- aggregate 持有关系不得随着中间 binding 的覆盖丢失；外层逃逸必须传播到后加入的 child。
-- unluac: expect-not-contains [[unluac error]]
-- unluac: expect-not-contains [[unresolved]]
-- 完整左值/读取/常量写帧不保留中转声明；外层调用恢复后也不产生 print 别名。
-- unluac: expect-ast-count [[local-decl]] [[0]] [[@proto=1]] [[@dialect=lua5.1]]
-- 外层仅保留 weak、child/inner/outer 和 repeat 的三份对象声明；末尾调用不另立 callee。
-- unluac: expect-ast-count [[local-decl]] [[7]] [[@proto=0]] [[@dialect=lua5.1]]
-- unluac: expect-not-contains [[ = print]] [[@dialect=lua5.1]]
local weak = setmetatable({}, { __mode = "v" })
local function clear(holder)
    weak[1] = holder.inner.child
    holder.inner.child = nil
    collectgarbage("collect")
    return weak[1] ~= nil
end

local child = {}
local inner = {}
local outer = { inner = inner }
inner.child = child
inner = nil
assert(clear(outer))
child = nil
collectgarbage("collect")
assert(weak[1] == nil)
print("regress_461_aggregate_escape_identity#1")

-- 未知 receiver 的 __index 会暴露 key，不能把一次读取当作未逃逸证明。
local function lookup_escape()
    local probe = setmetatable({}, {
        __index = function(_, key)
            weak[1] = key
            return 1
        end,
    })
    local value = {}
    local holder = { value = value }
    local result = probe[value]
    holder.value = nil
    collectgarbage("collect")
    assert(weak[1] ~= nil)
    value = nil
    collectgarbage("collect")
    assert(weak[1] == nil)
    -- Lua 5.1 的 GETUPVAL 目标快照先于 RHS；__index 改写 weak 后仍写入原表。
    -- 5.4/5.5 的 SETTABUP 有不同的 cell 读取时点，不套用这一方言专属断言。
    if _VERSION == "Lua 5.1" then
        local saved = weak
        local replacement = {}
        local value = {}
        local member = { child = value }
        local reads = 0
        local holder = setmetatable({}, {
            __index = function(_, key)
                assert(key == "inner")
                reads = reads + 1
                if reads == 1 then
                    weak = replacement
                else
                    assert(saved[1] == value and replacement[1] == nil)
                end
                return member
            end,
        })
        assert(not clear(holder))
        assert(reads == 2 and member.child == nil)
        assert(saved[1] == value and replacement[1] == nil)
        weak = saved
        weak[1] = nil
    end
    return result
end
assert(lookup_escape() == 1)

-- 已知 closure 的 child effect 必须向调用方传递 capture 的逃逸与写入。
local function capture_escape()
    local value = {}
    local holder = { value = value }
    local deliver = function() weak[1] = value end
    deliver()
    holder.value = nil
    collectgarbage("collect")
    assert(weak[1] ~= nil)
    value = nil
    collectgarbage("collect")
    assert(weak[1] == nil)
end
capture_escape()
print("regress_461_aggregate_escape_identity#2")

-- repeat 条件只能看到最外层 holder 时，也必须查询后加入的传递持有边。
local function check_alive()
    collectgarbage("collect")
    assert(weak[1] ~= nil)
    return true
end
repeat
    local child = {}
    local outer = { child = child }
    local value = {}
    child.value = value
    weak[1] = value
    value = nil
    child = nil
until check_alive()
collectgarbage("collect")
assert(weak[1] == nil)
print("regress_461_aggregate_escape_identity#3")

-- 回边和分支合流必须保持并行赋值前的两份对象身份，不能逐目标读取已更新的状态。
local function swap_holders(flag)
    local left = { marker = 11 }
    local right = { marker = 22 }
    local holder = {}
    local round = 0
    repeat
        if flag then
            left, right = right, left
        else
            left, right = left, right
        end
        holder.value = right
        round = round + 1
    until round == 3
    assert(left.marker == (flag and 22 or 11))
    local function deliver()
        weak[1] = holder.value
        holder.value = nil
    end
    deliver()
    collectgarbage("collect")
    assert(weak[1] == right)
    assert(right.marker == (flag and 11 or 22))
    right = nil
    collectgarbage("collect")
    collectgarbage("collect")
    assert(weak[1] == nil)
end
swap_holders(true)
swap_holders(false)
print("regress_461_aggregate_escape_identity#4")
