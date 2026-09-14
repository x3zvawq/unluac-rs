-- regress_642#1: repeat 的 break 必须跳过尾条件；有限外循环让多余的 __index 读取可观察。
-- unluac: expect-ast-min [[repeat]] [[1]]
-- unluac: expect-ast-min [[while]] [[1]]
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
