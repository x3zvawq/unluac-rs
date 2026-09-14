-- 两层 repeat 共享入口与外层 while latch；内层出口不能提前归为祖先 continue。
-- unluac: expect-ast-min [[repeat]] [[1]] [[@dialect=luau]]
-- unluac: expect-ast-max [[goto]] [[0]] [[@dialect=luau]]
local function run(mode)
    local step, x, reads = 0, 0, 0
    local xs = setmetatable({}, {__index = function()
        reads = reads + 1
        return true
    end})
    while step < 3 do
        step = step + 1
        x = x + 1
        repeat
            repeat
                if mode == 1 and step == 2 then break end
                if mode == 2 then break end
            until xs[step]
            if mode ~= 3 then break end
        until xs[step]
    end
    return step, x, reads
end
for mode = 1, 3 do
    local step, x, reads = run(mode)
    assert(step == 3 and x == 3)
    assert(reads == (mode == 1 and 2 or mode == 2 and 0 or 6))
    print("regress_643#1", mode, step, x, reads)
end
