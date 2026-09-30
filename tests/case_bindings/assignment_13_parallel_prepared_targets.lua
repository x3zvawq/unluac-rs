-- 左值快照与 RHS 结果各自保持原准备顺序，两个写回共同提交。
-- unluac: expect-ast-count [[local-decl]] [[0]] [[@proto=1]]
-- unluac: expect-ast-count [[assign]] [[1]] [[@proto=1]]
-- unluac: expect-ast-count [[local-decl]] [[0]] [[@proto=2]]
-- unluac: expect-ast-count [[local-decl]] [[0]] [[@proto=3]]
-- unluac: expect-ast-count [[assign]] [[1]] [[@proto=3]]
-- unluac: expect-ast-count [[assign]] [[1]] [[@proto=5]]

local target
local function write_targets(first, last)
    target[1], target[2] = first, last
end

local replacement = {}
local writes = {}
local original = setmetatable({}, { __newindex = function(destination, key, value)
    writes[#writes + 1] = {key, value, destination == replacement}
    target = replacement
end })
setmetatable(replacement, getmetatable(original))
target = original
write_targets("first", "last")
assert(#writes == 2)
assert(writes[1][1] == 2 and writes[1][2] == "last")
assert(writes[2][1] == 1 and writes[2][2] == "first")
-- GETTABUP 与 GETUPVAL/SETTABLE 的目标读取时机不同，由原编译结果比较写入身份。
print("parallel_target_identity", writes[1][3], writes[2][3])

local first_present, last_present = false, false
local function write_status(values)
    first_present, last_present = values[1] ~= nil, values[2] ~= nil
end

local reads = 0
local values = setmetatable({}, { __index = function(_, key)
    reads = reads + 1
    assert(key == reads)
    assert(first_present == false and last_present == false)
    return key
end })
write_status(values)
assert(reads == 2 and first_present and last_present)
write_status({})
assert(first_present == false and last_present == false)
print("parallel_prepared_targets", "OK")

-- 前三个值在 scratch 准备，末项直接写 last，再逆序写字段及两个捕获 local。
-- __index 观察全部旧值；__newindex 必须观察到 last 已写、first/second 尚未写。
local function write_lookup_pack()
    local first, second, last = 0, 0, 0
    local reads = 0
    local writes = 0
    local values = setmetatable({}, { __index = function(_, key)
        assert(first == 0 and second == 0 and last == 0)
        reads = reads + 1
        assert(reads == key)
        return key
    end })
    local target = setmetatable({}, { __newindex = function(_, key, value)
        assert(reads == 4 and first == 0 and second == 0 and last == 4)
        assert(key == "value" and value == 3)
        writes = writes + 1
        first, second = -1, -2
    end })
    first, second, target.value, last = values[1], values[2], values[3], values[4]
    assert(reads == 4 and writes == 1 and first == 1 and second == 2 and last == 4)
end
write_lookup_pack()
print("parallel_lookup_targets", "OK")

-- 两个上值 RHS 都先读取；首个逆序 SETTABLE 的回调改写 cell，不能影响第二次写入。
-- unluac: expect-ast-count [[local-decl]] [[0]] [[@proto=8]]
-- unluac: expect-ast-count [[assign]] [[1]] [[@proto=8]]
local first_rhs, last_rhs = {}, {}
local function write_rhs_snapshot(destination)
    destination[1], destination[2] = first_rhs, last_rhs
end
local expected_first, expected_last = first_rhs, last_rhs
local observed_rhs = {}
local rhs_target = setmetatable({}, { __newindex = function(destination, key, value)
    observed_rhs[#observed_rhs + 1] = value
    assert(key == 3 - #observed_rhs)
    first_rhs, last_rhs = {}, {}
    rawset(destination, key, value)
end })
write_rhs_snapshot(rhs_target)
assert(#observed_rhs == 2 and observed_rhs[1] == expected_last and observed_rhs[2] == expected_first)
assert(rhs_target[1] == expected_first and rhs_target[2] == expected_last)
assert(first_rhs ~= expected_first and last_rhs ~= expected_last)
print("parallel_upvalue_rhs_snapshot", "OK")

-- 动态 key 的运算改变目标 cell，第一次写回又改变它；观测各方言原有的快照时点。
local dynamic_target, dynamic_key
-- unluac: expect-ast-count [[local-binding]] [[0]] [[@proto=10]]
-- unluac: expect-ast-count [[assign]] [[1]] [[@proto=10]]
local function write_dynamic_keys(first, last)
    dynamic_target[dynamic_key + 1], dynamic_target[dynamic_key + 2] = first, last
end
local dynamic_writes = {}
local first_target, second_target, third_target = {}, {}, {}
local target_names = {[first_target] = "first", [second_target] = "second", [third_target] = "third"}
local target_metatable = {__newindex = function(destination, key, value)
    dynamic_writes[#dynamic_writes + 1] = target_names[destination] .. ":" .. key .. ":" .. value
    dynamic_target = first_target
end}
setmetatable(first_target, target_metatable)
setmetatable(second_target, target_metatable)
setmetatable(third_target, target_metatable)
local key_evaluations = 0
dynamic_key = setmetatable({}, {__add = function(_, index)
    key_evaluations = key_evaluations + 1
    assert(key_evaluations == index)
    dynamic_target = index == 1 and second_target or third_target
    return index
end})
dynamic_target = first_target
write_dynamic_keys("left", "right")
assert(key_evaluations == 2 and #dynamic_writes == 2)
assert(string.match(dynamic_writes[1], ":2:right$") and string.match(dynamic_writes[2], ":1:left$"))
print("parallel_dynamic_targets", table.concat(dynamic_writes, ","))
