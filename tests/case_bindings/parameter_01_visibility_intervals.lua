-- 父参数即使没有被捕获也参与参数避让；兄弟与已退出的局部作用域不能污染后续定义点。
-- unluac: expect-contains [[(b)]]
-- unluac: expect-contains [[(c)]]
-- unluac: expect-count [[(b)]] [[1]]
-- unluac: expect-count [[(c)]] [[1]]
-- unluac: expect-not-contains [[unluac error]]
-- 递归作用域、循环头和 until 的临时绑定不能抬高后继帧的源码槽位。
-- unluac: expect-ast-count [[empty-local]] [[0]]
-- unluac: expect-ast-count [[local-binding]] [[8]] [[@proto=0]]
-- unluac: expect-not-contains [[= assert]]
-- unluac: expect-contains [[= (function(]]
-- unluac: expect-contains [[until (function(]]
-- unluac: expect-contains [[assert(make(10)(20)(30) == 31)]] [[@debug=retained]]
-- unluac: expect-contains [[assert(factories[3](3) == 4 and factories[4](3) == 5)]] [[@debug=retained]]
-- unluac: expect-contains [[assert(count == 2)]] [[@debug=retained]]
local function make(a)
    print("parent", a)
    local function child(b)
        print("child", b)
        return function(c) return c + 1 end
    end
    return child
end
assert(make(10)(20)(30) == 31)

local factories = {}
do
    local function a(n)
        if n == 0 then return 7 end
        return a(n - 1)
    end
    factories[1] = function(x) return a(x) end
end
factories[2] = function(x) return x + 2 end
assert(factories[1](2) == 7 and factories[2](5) == 7)

for i = (function(x) return x end)(1), 2 do
    factories[2 + i] = function(x) return i + x end
end
for k, v in ipairs({8, 9}) do
    factories[4 + k] = function(x) return v + x end
end
assert(factories[3](3) == 4 and factories[4](3) == 5)
assert(factories[5](2) == 10 and factories[6](2) == 11)

local count = 0
repeat
    local value = count + 1
    count = value
until (function(x) return x == value end)(2)
assert(count == 2)
print("regress492", factories[2](40))
