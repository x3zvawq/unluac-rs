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
