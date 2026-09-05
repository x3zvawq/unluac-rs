-- 连续 debug 生命周期复用寄存器，并覆盖同起点多局部、嵌套遮蔽与闭包捕获。
-- unluac: expect-not-contains [[unluac error]]
-- unluac: expect-not-contains [[unresolved]]
local total = 0
local function consume(value)
    total = total + value
end
do local value = 1; consume(value) end
do local value = 2; consume(value) end
do local value = 3; consume(value) end
do local value = 4; consume(value) end
do local value = 5; consume(value) end
do local value = 6; consume(value) end
do local value = 7; consume(value) end
do local value = 8; consume(value) end
do local value = 9; consume(value) end
do local value = 10; consume(value) end
do local value = 11; consume(value) end
do local value = 12; consume(value) end
do local value = 13; consume(value) end
do local value = 14; consume(value) end
do local value = 15; consume(value) end
do local value = 16; consume(value) end
do local value = 17; consume(value) end
do local value = 18; consume(value) end
do local value = 19; consume(value) end
do local value = 20; consume(value) end
do local value = 21; consume(value) end
do local value = 22; consume(value) end
do local value = 23; consume(value) end
do local value = 24; consume(value) end
do local value = 25; consume(value) end
do local value = 26; consume(value) end
do local value = 27; consume(value) end
do local value = 28; consume(value) end
do local value = 29; consume(value) end
do local value = 30; consume(value) end
do local value = 31; consume(value) end
do local value = 32; consume(value) end
assert(total == 528)
local read
do
    local first, second = 4, 9
    do
        local first, second = second + 1, first + 2
        consume(first + second)
    end
    read = function() return first, second end
end
local first, second = read()
assert(first == 4 and second == 9)
assert(total == 544)
print("regress494", total, first, second)
