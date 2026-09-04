-- 同一 epoch 的多个捕获共享未来写入事实；不同 close epoch 的 cell 仍然独立。
-- unluac: expect-not-contains [[unluac error]]
-- unluac: expect-not-contains [[unresolved]]
local function branches(flag)
    local value = 10
    local first = function() return value end
    if flag then
        value = 20
    end
    local second = function() return value end
    if not flag then
        value = 30
    end
    assert(first() == (flag and 20 or 30))
    assert(second() == first())
end
branches(true)
branches(false)

local readers = {}
local value = 0
repeat
    value = value + 1
    readers[value] = function() return value end
until value == 3
-- 写入在静态捕获前，但回边会再次执行，三个闭包必须共享可写 cell。
assert(readers[1]() == 3 and readers[2]() == 3 and readers[3]() == 3)

do
    local value = 40
    readers[4] = function() return value end
    value = 41
end
do
    local value = 50
    readers[5] = function() return value end
end
do
    local value = 60
    if readers[4]() == 41 then
        value = 61
    end
    readers[6] = function() return value end
end
assert(readers[4]() == 41 and readers[5]() == 50 and readers[6]() == 61)
print("regress_475_capture_write_graph", "OK")
