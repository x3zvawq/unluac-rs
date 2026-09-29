-- regress_255_header_retry_terminal_state#1: direct sibling latch 保留 header-retry state
-- unluac: expect-not-contains [[end)(]]
-- unluac: expect-contains [[for ]]
-- unluac: expect-not-contains [[goto ]]
-- unluac: expect-not-contains [[::L]]
-- unluac: expect-not-contains [[unresolved]]
-- unluac: expect-not-contains [[unluac error]]
-- unluac: expect-ast-count [[repeat]] [[2]]
-- 原函数 iterator 与根块样本枚举各一处。
-- unluac: expect-ast-count [[generic-for]] [[2]]
-- 内层重试沿用外层状态；run 只保留三个状态及两个 iterator 绑定。
-- unluac: expect-ast-count [[local-binding]] [[5]] [[@dialect=lua5.1]] [[@proto=1]]
-- unluac: expect-ast-count [[local-binding]] [[5]] [[@dialect=luajit]] [[@proto=3]]
local function run(inner, iterator)
    local done, round, count = false, 0, 0
    repeat
        repeat
            for key, value in iterator do
                count = count + key + value
            end
        until not inner
        if done and inner then break end
        round = round + 1
        done = round > 1
    until done
    return round, count
end

local function once(_, control)
    if control == nil then return 1, 1 end
end

local round, count = run(false, once)
assert(round == 2, round)
assert(count == 4, count)
print("regress_255_header_retry_terminal_state#1", round, count)

-- inner 为真时内层 repeat 不终止；空、单次和多次 iterator 检查有限路径的入口交接。
for _, size in ipairs({ 0, 1, 3 }) do
    local calls = 0
    local function iterator(_, control)
        calls = calls + 1
        local next_key = (control or 0) + 1
        if next_key <= size then return next_key, next_key * 2 end
    end
    local actual_round, actual_count = run(false, iterator)
    assert(actual_round == 2)
    assert(actual_count == 3 * size * (size + 1))
    assert(calls == 2 * (size + 1))
end
