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

-- 首项常量在高槽准备，末项由 RK 直接写入；后继调用复用准备槽仍须保持逆序写回。
local function write_literals()
    local seen = {}
    local sink = setmetatable({}, {__newindex = function(_, key, value)
        seen[#seen + 1] = key .. ":" .. tostring(value)
    end})
    sink.first, sink.second = false, true
    assert(table.concat(seen, ",") == "second:true,first:false")
    sink.first, sink.second = 17, "tail"
    assert(table.concat(seen, ",") == "second:true,first:false,second:tail,first:17")
    sink.first, sink.second = nil, false
    assert(table.concat(seen, ",") == "second:true,first:false,second:tail,first:17,second:false,first:nil")
end
write_literals()

-- 中间 RK 字段写不覆盖构造器高槽，元方法仍能观察刚发布的空表；后继参数覆盖才结束根。
local function publish_empty(holder, observer, finish)
    holder.target.value = {}
    observer.tick = 1
    finish("done")
end
local weak = setmetatable({}, {__mode = "v"})
local events = {}
local holder = {target = setmetatable({}, {__newindex = function(_, key, value)
    assert(key == "value")
    weak[1] = value
    events[#events + 1] = "write"
end})}
local observer = setmetatable({}, {__newindex = function(_, key, value)
    assert(key == "tick" and value == 1)
    collectgarbage("collect")
    collectgarbage("collect")
    assert(weak[1] ~= nil)
    events[#events + 1] = "observe"
end})
local function finish(marker)
    assert(marker == "done")
    collectgarbage("collect")
    collectgarbage("collect")
    assert(weak[1] == nil)
    events[#events + 1] = "finish"
end
publish_empty(holder, observer, finish)
assert(table.concat(events, ",") == "write,observe,finish")
-- 常量准备和空表发布由完整赋值帧消费，不额外物化高槽 holder。
-- unluac: expect-ast-count [[local-binding]] [[2]] [[@proto=5]]
-- unluac: expect-ast-count [[assign]] [[3]] [[@proto=5]]
-- unluac: expect-ast-count [[local-binding]] [[0]] [[@proto=7]]
-- unluac: expect-ast-count [[assign]] [[2]] [[@proto=7]]
-- unluac: expect-ast-count [[call]] [[1]] [[@proto=7]]

-- 字面量和空表共同准备后才逆序发布到捕获 cell；每次分配仍产生独立对象。
local function literal_allocations()
    local left, right = true, "old"
    local function observe(expected, previous)
        assert(left == expected and type(right) == "table" and right ~= previous)
        return right
    end
    local previous = right
    left, right = nil, {}
    previous = observe(nil, previous)
    left, right = false, {}
    previous = observe(false, previous)
    left, right = 17, {}
    previous = observe(17, previous)
    left, right = "value", {}
    previous = observe("value", previous)
    left, right = {}, {}
    assert(type(left) == "table" and left ~= right)
    observe(left, previous)
end
literal_allocations()
-- 只保留两个目标 cell、观察函数和上一对象，不能把 RHS scratch 变成源码绑定。
-- unluac: expect-ast-count [[local-binding]] [[4]] [[@proto=11]]
-- unluac: expect-ast-count [[assign]] [[9]] [[@proto=11]]
-- unluac: expect-ast-count [[local-binding]] [[0]] [[@proto=12]]
