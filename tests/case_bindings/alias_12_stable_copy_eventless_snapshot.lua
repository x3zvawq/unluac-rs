-- 稳定 truthiness 仍保留调用前缀；完整 RETURN 事务只消除结果区副本，保持快照与元方法次数。
-- unluac: expect-contains [[return r1_0, r1_0]]
-- unluac: expect-contains [[local r1_0 = not p1_0]]
-- 选值稳定仍不足以删声明：原 sink CALL 的高槽残根在返回后可被 caller 观察。
-- unluac: expect-ast-count [[local-decl]] [[1]] [[@proto=2]]
-- unluac: expect-contains [[return r2_0]]
-- unluac: expect-contains [[local r3_0 = not p3_0]]
-- unluac: expect-contains [[local r5_0 = p5_0 == p5_1]]
-- unluac: expect-contains [[p8_1(r8_0)]]
-- unluac: expect-contains [[local r8_0 = not p8_0]]
-- unluac: expect-contains [[local r9_0 = not p9_0]]
-- unluac: expect-contains [[p10_1[1] = not p10_0]]
-- unluac: expect-not-contains [[local r10_0 = not p10_0]]
-- unluac: expect-contains [[p11_1(r11_0)]]
-- unluac: expect-contains [[local r11_0 = p11_0]]
-- 值快照相同仍须保持原 COPY 链的高槽残根及声明前缀。
-- unluac: expect-contains [[until r13_2]]
-- unluac: expect-contains [[local r13_0 = p13_0]]
-- unluac: expect-ast-count [[repeat-condition-local]] [[1]] [[@proto=13]]
-- unluac: expect-ast-max [[local-decl]] [[4]] [[@proto=13]]
-- unluac: expect-contains [[r14_0 = p14_0]]
-- 原 nil 初始化与 COPY 在同一 repeat 词法身份上交接；不能在函数入口另造 holder。
-- unluac: expect-ast-count [[repeat-condition-local]] [[1]] [[@proto=14]]
-- unluac: expect-ast-max [[local-decl]] [[4]] [[@proto=14]]
-- unluac: expect-ast-count [[do-block]] [[1]] [[@proto=14]]
-- unluac: expect-ast-count [[empty-local]] [[0]] [[@proto=14]]
-- 参数槽覆盖必须保留；另建 local 会让被覆盖的旧参数继续成为强根。
-- unluac: expect-contains [[until p15_0]]
-- unluac: expect-contains [[return p15_0]]
-- unluac: expect-ast-count [[empty-local]] [[0]] [[@proto=15]]
-- 捕获的初始化保留结果绑定；嵌套比较与后继构造器不新增 callee/operand 交接。
-- unluac: expect-ast-count [[local-decl]] [[17]] [[@proto=0]]
-- unluac: expect-not-contains [[= assert]]
-- unluac: expect-contains [[[2] == (_VERSION ~= "Lua 5.1"))]]
-- 计算左值与 Boolean RHS 共用原赋值帧；短路返回共用原 RETURN 槽。
-- unluac: expect-ast-count [[local-decl]] [[0]] [[@proto=21]]
-- unluac: expect-ast-count [[local-decl]] [[0]] [[@proto=25]]
-- unluac: expect-contains [[return p25_0 and p25_1 or p25_2]]

local function stable_not(value, sink)
    local inverted = not value
    sink()
    return inverted, inverted
end

local function stable_choice(flag, left, right, sink)
    local selected = (flag and left) or right
    sink()
    return selected
end

local function written_dependency(value)
    local inverted = not value
    value = true
    return inverted
end

local comparison_hits = 0
local equality = {
    __eq = function()
        comparison_hits = comparison_hits + 1
        return true
    end,
}

local function compared_twice(left, right)
    local equal = left == right
    return equal, equal
end

local function captured_dependency(value)
    local inverted = not value
    local function mutate()
        value = true
    end
    mutate()
    return inverted
end

local function write_after_last_use(value, sink)
    local inverted = not value
    sink()
    sink(inverted)
    value = true
end

local function repeated_dependency(value)
    local inverted = not value
    local count = 0
    while inverted and count < 2 do
        count = count + 1
        value = true
    end
    return count
end

local function same_owner_write(value, sink)
    local inverted = not value
    value, sink[1] = true, inverted
end

local function stable_parameter(value, sink)
    local alias = value
    sink()
    sink(alias)
end

local function allocated_twice()
    local value = {}
    return value, value
end

local function local_decl_handoff(seed)
    repeat
        local source = seed
        local alias = source
        local target = alias
        source = {}
    until target
    return true
end

local function parallel_handoff(seed)
    repeat
        local source = seed
        local alias = source
        local target, marker
        target, marker = alias, "parallel"
        source = {}
    until target
    return true
end

local function parameter_handoff(target, seed)
    repeat
        local source = seed
        local alias = source
        target = alias
        source = {}
    until target
    return target
end

local first, second = stable_not(false, function() end)
assert(first == true and second == true)

local left = setmetatable({}, equality)
local right = setmetatable({}, equality)
assert(stable_choice(true, left, right, function() end) == left)
assert(stable_choice(false, left, right, function() end) == right)
assert(written_dependency(false) == true)
assert(captured_dependency(false) == true)

local seen = {}
write_after_last_use(false, function(value)
    if value ~= nil then
        seen[#seen + 1] = value
    end
end)
assert(#seen == 1 and seen[1] == true)
assert(repeated_dependency(false) == 2)
local same_owner_seen = {}
same_owner_write(false, same_owner_seen)
assert(same_owner_seen[1] == true)
stable_parameter("parameter", function(value)
    if value ~= nil then
        seen[#seen + 1] = value
    end
end)
assert(seen[2] == "parameter")

local equal_first, equal_second = compared_twice(left, right)
assert(equal_first == true and equal_second == true)
assert(comparison_hits == 1)

local allocated_first, allocated_second = allocated_twice()
assert(allocated_first == allocated_second)

local handoff_seed = {}
assert(local_decl_handoff(handoff_seed) == true)
assert(parallel_handoff(handoff_seed) == true)
assert(parameter_handoff(nil, handoff_seed) == handoff_seed)

-- 对照有/无 selected 的原帧，固定单返回 seed 把 weak resource 留在待覆盖 scratch。
local scratch_weak = setmetatable({}, { __mode = "v" })
local scratch_seen = {}
local scratch_environment = setmetatable({}, {
    __newindex = function()
        collectgarbage("collect")
        scratch_seen[#scratch_seen + 1] = scratch_weak[1] ~= nil
    end,
})
local function make_scratch_sink(environment)
    local _ENV = environment
    return function() scratch_marker = true end
end
local scratch_sink = make_scratch_sink(scratch_environment)
local function seed_scratch(a, b, c, d, e, resource)
    scratch_weak[1] = resource
    return true
end
local function inline_choice(flag, left, right, observer)
    observer()
    return (flag and left) or right
end
local function drive_original()
    do local dummy = seed_scratch(false, false, false, false, false, {}) end
    stable_choice(true, false, false, scratch_sink)
    return true
end
local function drive_inline()
    do local dummy = seed_scratch(false, false, false, false, false, {}) end
    inline_choice(true, false, false, scratch_sink)
    return true
end
-- Lua 5.1 的环境协议为 setfenv；其它方言使用上面的词法 _ENV。
if setfenv then setfenv(scratch_sink, scratch_environment) end
drive_original()
drive_inline()
assert(scratch_seen[1] == false)
assert(scratch_seen[2] == (_VERSION ~= "Lua 5.1"))

-- 连续参数转发与删除链的对照：caller 覆盖三个低槽后，原 r3 仍能保根。
local function inline_handoff(seed)
    repeat
        local discarded = {}
    until seed
    return true
end
local handoff_weak = setmetatable({}, {__mode = "v"})
local handoff_observations = {}
local function make_handoff_value()
    local value = {}
    handoff_weak.value = value
    return value
end
local handoff_methods = setmetatable({}, {__index = function()
    collectgarbage("collect")
    collectgarbage("collect")
    handoff_observations[#handoff_observations + 1] = type(handoff_weak.value)
    return function() end
end})
local function observe_handoff(callback)
    callback(make_handoff_value())
    local a, b, c = 1, 1, 1
    handoff_methods.observe()
    -- 保持高槽位于 caller 实际 frame 内，观察低槽覆盖后的剩余根。
    local reserve = {1, 2, 3, 4, 5, 6, 7, 8, 9, 10}
    return reserve[1]
end
collectgarbage("stop")
observe_handoff(local_decl_handoff)
observe_handoff(inline_handoff)
collectgarbage("restart")
assert(table.concat(handoff_observations, ",") == "table,nil")

-- 复用同一观察器；参数原槽已被 true 覆盖，返回后不应残留传入对象。
local function observe_parameter_handoff(callback)
    callback(make_handoff_value(), true)
    handoff_methods.observe()
    local reserve = {1, 2, 3, 4, 5, 6, 7, 8, 9, 10}
    return reserve[1]
end
collectgarbage("stop")
observe_parameter_handoff(parameter_handoff)
collectgarbage("restart")
assert(handoff_observations[3] == "nil")

-- 用被调 closure 自身的残根覆盖 Lua 5.1；前面的旧 scratch 探针对该方言无区分力。
local function make_choice_sink()
    local marker = {}
    local sink = function() return marker end
    handoff_weak.value = sink
    return sink
end
local function observe_choice(callback)
    callback(true, false, false, make_choice_sink())
    local a, b, c, d, e = 1, 1, 1, 1, 1
    handoff_methods.observe()
    local reserve = {1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14}
    return reserve[1]
end
collectgarbage("stop")
observe_choice(stable_choice)
observe_choice(inline_choice)
collectgarbage("restart")
assert(handoff_observations[4] == "function")
assert(handoff_observations[5] == "nil")

-- parallel 交接同样保留高槽参数根；复用已固定三个低槽覆盖的 caller。
collectgarbage("stop")
observe_handoff(parallel_handoff)
observe_handoff(inline_handoff)
collectgarbage("restart")
assert(handoff_observations[6] == "table")
assert(handoff_observations[7] == "nil")

-- caller 的旧高槽对象不属于 callee 参数；额外 NEWTABLE scratch 会过早覆盖它。
local function seed_handoff_scratch(a, b, c, d, e, f, resource)
    handoff_weak.value = resource
    return true
end
local function observe_handoff_allocation(callback)
    do local result = seed_handoff_scratch(false, false, false, false, false, false, {}) end
    callback(true)
    handoff_methods.observe()
    local reserve = {1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12}
    return reserve[1]
end
collectgarbage("stop")
observe_handoff_allocation(parallel_handoff)
collectgarbage("restart")
assert(handoff_observations[8] == "table")

-- 相邻低槽必须仍被原 COPY/NEWTABLE 覆盖；只让更高槽对象存活不足以证明帧正确。
local function seed_handoff_lower_scratch(a, b, c, d, e, resource)
    handoff_weak.value = resource
    return true
end
local function observe_handoff_lower_allocation(callback)
    do local result = seed_handoff_lower_scratch(false, false, false, false, false, {}) end
    callback(true)
    handoff_methods.observe()
    local reserve = {1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12}
    return reserve[1]
end
collectgarbage("stop")
observe_handoff_lower_allocation(parallel_handoff)
collectgarbage("restart")
assert(handoff_observations[9] == "nil")
