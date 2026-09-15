-- 连续纯依赖移入普通赋值；无关前缀、捕获和求值事件仍保留自己的边界。
-- unluac: expect-ast-count [[repeat]] [[1]]
local function fill(box, value)
    local unrelated = value
    local result = not value
    result = not result; result = not result; result = not result; result = not result
    result = not result; result = not result; result = not result; result = not result
    result = not result; result = not result; result = not result; result = not result
    result = not result; result = not result; result = not result; result = not result
    result = not result; result = not result; result = not result; result = not result
    result = not result; result = not result; result = not result; result = not result
    result = not result; result = not result; result = not result; result = not result
    result = not result; result = not result; result = not result; result = not result
    result = result == true
    result = not result
    box.value = result
end
local box = {}
fill(box, nil); assert(box.value == false)
fill(box, false); assert(box.value == false)
fill(box, 0); assert(box.value == true)
fill(box, ""); assert(box.value == true)

local events = 0
local flag = false
local function key()
    events = events + 1
    flag = true
    return "event"
end
local snapshot = not flag
snapshot = not snapshot
snapshot = not snapshot
box[key()] = snapshot
assert(box.event == true and flag == true and events == 1)

-- 查找事件同样不能把旧快照变为回调后的读取。
flag = false
local holder = setmetatable({}, {__index = function()
    events = events + 1
    flag = true
    return box
end})
snapshot = not flag
snapshot = not snapshot
snapshot = not snapshot
holder.target.lookup = snapshot
assert(box.lookup == true and flag == true and events == 2)

local captured = false
local function read() return captured end
captured = not captured
captured = not captured
captured = not captured
box.capture = captured
assert(read() == true and box.capture == true)

-- 额外 use 和回边状态都不能被当成单次 forwarding producer 删除。
local result = false
local count = 0
repeat
    result = not result
    count = count + 1
until count == 3
box.loop = result
assert(result == true and box.loop == true)

local function split(value)
    local first = not value
    local second = not first
    box.first = first
    box.second = second
end
split(nil)
assert(box.first == true and box.second == false)
split(0)
assert(box.first == false and box.second == true)
print("regress_548_pure_assignment_suffix", "OK")
