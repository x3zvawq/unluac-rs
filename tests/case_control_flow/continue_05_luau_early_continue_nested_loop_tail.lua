-- regress_118_luau_early_continue_nested_loop_tail#1: early-continue guard 不抢占 nested generic-for tail
-- unluac: expect-contains [[repeat]]
-- unluac: expect-contains [[for ]]
-- unluac: expect-contains [[if p1_0 then]]
-- unluac: expect-not-contains [[goto ]]
-- unluac: expect-not-contains [[::L]]
-- unluac: expect-not-contains [[unresolved]]
-- unluac: expect-not-contains [[unluac error]]
-- unluac: expect-not-contains [[r1_0 = r1_3]]
-- unluac: expect-ast-count [[generic-for]] [[2]] [[@proto=1]]
-- unluac: expect-ast-count [[repeat]] [[1]] [[@proto=1]]
-- unluac: expect-ast-count [[if]] [[4]] [[@proto=1]]
-- unluac: expect-ast-count [[break]] [[2]] [[@proto=1]]
-- unluac: expect-ast-count [[continue]] [[1]] [[@proto=1]]
-- unluac: expect-ast-count [[local-decl]] [[1]] [[@proto=1]]
-- unluac: expect-ast-count [[empty-local]] [[0]] [[@proto=1]]
-- 内层循环的三次原始加法不能按常量结果消除。
-- unluac: expect-contains [[+ 1 + 1 + 1]]
local function run(a, b, c, xs)
    local x = 0
    for k, v in xs do
        repeat
            if a then
                if xs[x] then break end
            else
                repeat
                    break
                until b
                if xs[x] then break end
                if a then continue end
            end
            for inner_k, inner_v in xs do
                x = x + 1
                x = x + 1
                x = x + 1
            end
        until b
    end
    return x
end

print("regress_118_luau_early_continue_nested_loop_tail#1", run(false, true, false, { 1, 2 }))
print("regress_118_luau_early_continue_nested_loop_tail#2", run(true, true, false, { 1, 2 }))
print(
    "regress_118_luau_early_continue_nested_loop_tail#3",
    run(false, true, false, { [0] = true, 1, 2 })
)

-- a 为固定参数，else 中的 continue 本身不可达，仍保留原控制结构。
-- b=false 时每第三次索引退出 repeat，实际执行多轮共享的内层循环。
for _, a in ipairs({true, false}) do
    for _, b in ipairs({true, false}) do
        for _, hit in ipairs({true, false}) do
            local reads = 0
            local xs = setmetatable({1, 2}, {__index = function(_, key)
                reads = reads + 1
                assert(reads <= 6)
                if hit then
                    assert(key == 0)
                elseif b then
                    assert(key == 6 * (reads - 1))
                else
                    assert(key == 6 * (reads - 1 - math.floor((reads - 1) / 3)))
                end
                return hit or (not b and reads % 3 == 0)
            end})
            local expected = hit and 0 or (b and 12 or 24)
            assert(run(a, b, false, xs) == expected)
            assert(reads == ((hit or b) and 2 or 6))
            print("early continue nested tail", a, b, hit, reads, expected)
        end
    end
end
