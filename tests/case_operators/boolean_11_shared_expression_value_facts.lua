-- 正常结果事实不能替代求值事件证明；falsy 结果也不能被统一改成 false。
-- unluac: expect-not-contains [[unresolved]]
-- unluac: expect-not-contains [[unluac error]]
-- unluac: expect-contains [[return p2_0 and false]] [[@dialect=lua5.4]]
-- unluac: expect-ast-count [[table-list-field]] [[3]] [[@proto=5]] [[@dialect=luajit]]
-- unluac: expect-ast-max [[local-decl]] [[2]] [[@proto=5]] [[@dialect=luajit]]
-- 前两个 result 比较的完整参数帧不能拆成 callee 与 Boolean local；再生成也保持此结构。
-- unluac: expect-contains [[assert(r0_8[1] == r0_5 and r0_8[2] == r0_5 and r0_8[3] == true)]] [[@dialect=luajit]]
-- unluac: expect-contains [[assert(r0_8[1] == nil and r0_8[2] == nil and r0_8[3] == true)]] [[@dialect=luajit]]
-- 原比较的 Boolean 物化事实应保留，不交替生成 if 与空 local。
-- unluac: expect-contains [[assert(not r0_10 and r0_0 == 9)]] [[@dialect=luajit]]
-- TDUP 的初始 hash marker 由同批真实字段承接，不能按模板遍历顺序重复发射。
-- unluac: expect-not-contains [[__add = nil]] [[@dialect=luajit]]
-- unluac: expect-not-contains [[__unm = nil]] [[@dialect=luajit]]
-- unluac: expect-not-contains [[__lt = nil]] [[@dialect=luajit]]
local events = 0
local function mark(value)
    events = events + 1
    return value
end

local function falsy(value)
    return (value and false) and true
end
assert(falsy(nil) == nil)
assert(falsy(false) == false)
assert(falsy({}) == false)
assert(falsy(0) == false and falsy("") == false)

local function selected_number(flag)
    if (mark(flag) and 2 or 3) + 4 then
        return 7
    end
    return 9
end
assert(selected_number(false) == 7)
assert(selected_number(true) == 7)
assert(events == 2)

local function selected_value(flag, a, b)
    local value
    if flag then value = a else value = b end
    return value and true
end
assert(selected_value(true, nil, {}) == nil)
assert(selected_value(false, {}, false) == false)
assert(selected_value(true, {}, nil) == true)

local object = {}
local operand = setmetatable({}, {
    __add = function() events = events + 1; return object end,
    __unm = function() events = events + 1; return object end,
    __lt = function() events = events + 1; return true end,
})
local function arithmetic(value)
    local result = value + 1
    return { result, -value, value < value }
end
local result = arithmetic(operand)
assert(result[1] == object and result[2] == object and result[3] == true)
assert(events == 5)
object = nil
result = arithmetic(operand)
assert(result[1] == nil and result[2] == nil and result[3] == true)
assert(events == 8)
-- nil-hole 的边界由各 VM 的原始运行作 oracle，不跨方言硬编码一个长度。
print("nil-hole-length", #result)

local function failing()
    if (mark(true) and error("expected") or 2) + 4 then
        events = events + 100
    end
end
local ok = pcall(failing)
assert(not ok and events == 9)

-- 批次中的临时对象必须跨过后续元方法，返回后只由结果表继续持有。
local weak = setmetatable({}, { __mode = "v" })
local source = setmetatable({}, {
    __add = function() return nil end,
    __unm = function()
        local value = {}
        weak[1] = value
        return value
    end,
    __lt = function()
        collectgarbage("collect")
        collectgarbage("collect")
        assert(weak[1] ~= nil)
        return true
    end,
})
result = arithmetic(source)
assert(result[1] == nil and result[2] == weak[1] and result[3] == true)
result[2] = nil
collectgarbage("collect")
collectgarbage("collect")
assert(weak[1] == nil)
print("regress_468_shared_expression_value_facts", "OK")

-- 相同 CALL 语法不代表同一稳定 binding；falsy 路径仍须执行两次。
events = 0
assert((not mark(nil) and mark(nil)) == nil)
assert(events == 2)

-- 复用现有计数回调作 __index：比较参数的两个 lookup 及短路右臂各执行一次。
-- 256 超出 LuaJIT TGETB 的内嵌键范围，必须继续保留其真实键准备协议。
local indexing = getmetatable(operand).__lt
local indexed_left = setmetatable({}, { __index = indexing })
local indexed_right = setmetatable({}, { __index = indexing })
events = 0
assert(indexed_left[1] == indexed_right[1] and indexed_left[2] == true)
assert(events == 3)
events = 0
assert(indexed_left[256] == indexed_right[256])
assert(events == 2)
