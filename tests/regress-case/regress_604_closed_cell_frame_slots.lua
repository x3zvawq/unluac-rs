-- 退出词法块后复用源码位置，不把原 cell epoch 合并或要求它归零。
local first, later
do
    local value = 1
    first = function() return value end
    later = function() return value end
    value = 3
end
assert(first() == 3 and later() == 3)

-- 新 local 可以占据已退出 cell 的原物理位置；旧闭包继续观察旧 cell。
local next_first, next_later
do
    local value = 4
    next_first = function() return value end
    next_later = function() return value end
    value = 9
end
assert(next_first() == 9 and next_later() == 9)
assert(first() == 3 and later() == 3)
print("closed-cell-slots", first(), later(), next_first(), next_later())
