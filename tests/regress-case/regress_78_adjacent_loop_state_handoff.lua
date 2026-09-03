-- regress_78_adjacent_loop_state_handoff#1: adjacent loops share the first loop exit state
-- 两个分支均退出时可消除条件壳，但不能丢掉索引读取或换掉前一循环的出口值。
-- 方言可把后一循环恢复为 repeat 或 while；binding 编号也不是交接合同。
-- unluac: expect-not-contains [[goto ]]
-- unluac: expect-not-contains [[::L]]
-- unluac: expect-not-contains [[unluac error]]
local function run(a, b, xs)
    local x = 0
    for _ = 1, 3 do
        x = x + 1
    end
    repeat
        if a then
            if xs[x] then
                break
            end
            break
        elseif a and b then
            break
        end
    until a
    return x
end

print("regress_78_adjacent_loop_state_handoff#1", run(true, false, { [3] = true }))

for _, hit in ipairs({ true, false }) do
    local reads = {}
    local xs = setmetatable({}, {
        __index = function(_, index)
            reads[#reads + 1] = index
            return hit
        end,
    })
    assert(run(true, false, xs) == 3)
    assert(#reads == 1 and reads[1] == 3, "second loop must read the first loop exit state once")
end
