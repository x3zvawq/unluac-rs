-- 已知 child 的 capture 效果必须贯穿每个 root 消费者：读、写、返回和间接调用不同。
-- unluac: expect-not-contains [[unresolved]]
-- unluac: expect-not-contains [[unluac error]]
local weak = setmetatable({}, { __mode = "v" })
local function collect()
    collectgarbage("collect")
    collectgarbage("collect")
end

-- 单纯 truthiness 读取不发布 capture，也不修改它。
local function read_capture()
    local value = {}
    local function read()
        if value then return 7 end
        return 3
    end
    assert(read() == 7)
    value = nil
    assert(read() == 3)
end
read_capture()

-- 写入 capture 的调用替换当前对象；原值在写入后应当能够回收。
local function write_capture()
    local value = {}
    weak[1] = value
    local function replace()
        value = {}
    end
    replace()
    collect()
    assert(weak[1] == nil)
    assert(value ~= nil)
end
write_capture()

-- factory 返回 closure 后，投影后的 capture 发布效果仍属于原 producer。
local function returned_capture()
    local value = {}
    local function factory()
        return function() weak[1] = value end
    end
    local publish = factory()
    publish()
    collect()
    assert(weak[1] ~= nil)
    value = nil
    collect()
    assert(weak[1] == nil)
end
returned_capture()

-- child 调用作为 upvalue 捕获的 callee，必须继续投影 callee 的写入/逃逸效果。
local function called_capture()
    local value = {}
    local function publish() weak[1] = value end
    local function invoke() publish() end
    invoke()
    collect()
    assert(weak[1] ~= nil)
    value = nil
    collect()
    assert(weak[1] == nil)
end
called_capture()
print("regress_467_shared_child_root_effects", "OK")
