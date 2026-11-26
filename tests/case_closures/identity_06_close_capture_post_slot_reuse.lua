-- regress_273_close_capture_post_slot_reuse: Close 后复用物理槽不得越过循环体 local 的词法边界
-- 根函数保留两个迭代绑定；assert 的动态索引参数不另建中转 local。
-- 循环内同一 value 供读写闭包共享，不引入捕获交接绑定。

local function build()
    local readers = {}
    local writers = {}
    local index = 0

    while index < 2 do
        index = index + 1
        local value = index
        readers[index] = function()
            return value
        end
        writers[index] = function(delta)
            value = value + delta
        end
        value = value * 10
    end

    return readers, writers
end

local globals_before = {}
for key in pairs(_G) do
    globals_before[key] = true
end

local readers, writers = build()
for key in pairs(_G) do
    assert(globals_before[key], "unexpected global: " .. tostring(key))
end

assert(readers[1]() == 10)
assert(readers[2]() == 20)
writers[1](100)
assert(readers[1]() == 110)
assert(readers[2]() == 20)
writers[2](1000)
assert(readers[1]() == 110)
assert(readers[2]() == 1020)
print("regress_273_close_capture_post_slot_reuse")
