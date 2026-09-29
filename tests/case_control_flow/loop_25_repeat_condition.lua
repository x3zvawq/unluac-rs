-- regress_270_luau_repeat_condition#1: repeat 的 early-continue 不能丢掉条件状态写回
-- unluac: expect-contains [[repeat]]
-- unluac: expect-not-contains [[goto ]]
-- unluac: expect-not-contains [[::L]]
-- unluac: expect-not-contains [[unresolved]]
-- unluac: expect-not-contains [[unluac error]]

local function run(a, b, xs)
    local x = 0
    for i = 1, 3 do
        x += 1
        repeat
            local done
            if a then
                if xs[x] then
                    break
                end
                if a then
                    continue
                end
                x += 1
            end
            x += 1
            done = b
        until done
    end
    return x
end

local result = run(false, true, {})
assert(result == 6)
print("regress_270_luau_repeat_condition#1", result)

assert(run(nil, 0, {}) == 6)
assert(run(false, "", {}) == 6)
assert(run(true, nil, {true, true, true}) == 3)
-- 每个 x 首次读取为 false，实际走 continue；第二次读取退出该 repeat。
local reads, trace = 0, {}
local changing = setmetatable({}, {__index = function(_, key)
    reads = reads + 1
    trace[#trace + 1] = key
    assert(key == math.floor((reads + 1) / 2))
    return reads % 2 == 0
end})
assert(run(0, false, changing) == 3)
assert(reads == 6 and table.concat(trace, ",") == "1,1,2,2,3,3")
-- 原 x、数值循环 i 和 repeat 内 done 共三个绑定；不保留机械回边 carrier。
-- unluac: expect-ast-count [[local-binding]] [[3]] [[@proto=1]]
-- unluac: expect-ast-count [[repeat]] [[1]] [[@proto=1]]
-- unluac: expect-ast-count [[numeric-for]] [[1]] [[@proto=1]]
-- unluac: expect-ast-count [[continue]] [[1]] [[@proto=1]]
-- unluac: expect-ast-count [[break]] [[1]] [[@proto=1]]
-- unluac: expect-ast-count [[if]] [[3]] [[@proto=1]]
-- unluac: expect-ast-count [[local-binding]] [[5]] [[@proto=0]]
-- unluac: expect-ast-count [[local-binding]] [[0]] [[@proto=2]]
