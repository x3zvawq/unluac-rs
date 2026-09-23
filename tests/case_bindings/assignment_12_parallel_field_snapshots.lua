-- 第二项先写入，元方法改写两个源变量后，第一项仍必须使用写入前的快照。
-- unluac: expect-ast-count [[local-binding]] [[2]] [[@proto=1]]
-- unluac: expect-ast-count [[local-binding]] [[0]] [[@proto=2]]
-- unluac: expect-ast-count [[local-binding]] [[0]] [[@proto=3]]
-- unluac: expect-not-contains [[ = assert]]
local function write_fields(left, right)
    local seen = {}
    local sink = setmetatable({}, { __newindex = function(_, key, value)
        seen[#seen + 1] = {key, value}
        left, right = "changed-left", "changed-right"
    end })
    sink.first, sink.second = left, right
    assert(seen[1][1] == "second" and seen[2][1] == "first")
    return seen[1][2], seen[2][2], left, right
end

local left, right = {}, {}
local second, first, changed_left, changed_right = write_fields(left, right)
assert(first == left and second == right)
assert(changed_left == "changed-left" and changed_right == "changed-right")

-- 动态 key 的 __len 可以切换目标 upvalue；构造器 RHS 不能把目标读取提到 key 前。
local target
local function append_pair(first, second)
    target[#target + 1] = {first, second}
end
local replacement = {}
local length_called = false
local original = setmetatable({}, { __len = function()
    length_called = true
    target = replacement
    return 0
end })
target = original
append_pair(left, right)
local written = length_called and replacement or original
assert(written[1][1] == left and written[1][2] == right)
print("parallel_field_snapshots", "OK")
