-- regress_642#1: repeat 的 break 必须跳过尾条件；有限外循环让多余的 __index 读取可观察。
-- unluac: expect-ast-min [[repeat]] [[1]]
-- unluac: expect-ast-count [[while]] [[1]]
-- unluac: expect-ast-count [[if]] [[3]]
-- 编译器内联部分 run 调用后，剩余断言与输出仍应恢复直接调用。
-- unluac: expect-count [[assert(]] [[5]]
-- unluac: expect-count [[print(]] [[2]]
-- O2 的原计数操作由现存 run 重新展开，根函数不遗留高槽循环状态或调用别名。
-- unluac: expect-contains [[--!optimize 2]] [[@variant=O2]]
-- unluac: expect-ast-count [[local-binding]] [[3]] [[@proto=0]] [[@variant=O2]]
-- unluac: expect-ast-count [[repeat]] [[0]] [[@proto=0]] [[@variant=O2]]
-- 内联形参复用同一物理槽时，父级 xs 的初始化及长作用域身份仍应保留。
-- unluac: expect-contains [[local xs = setmetatable(]] [[@variant=O2]] [[@debug=retained]]
local function run(a, b, c, xs)
    local x = 0
    while a do
        x = x + 1
        if x > 2 then break end
        repeat
            if b then
                if c then
                    break
                else
                    print(x)
                end
            end
            if a then
                break
            end
        until xs[x]
    end
    return x
end

local reads = 0
local xs = setmetatable({}, {
    __index = function()
        reads = reads + 1
        return true
    end
})
assert(run(true, true, true, xs) == 3)
assert(run(true, true, false, xs) == 3)
assert(run(true, false, true, xs) == 3)
assert(run(false, true, true, xs) == 0)
assert(reads == 0, "repeat break must skip the condition")
print("regress_642#1", reads)
