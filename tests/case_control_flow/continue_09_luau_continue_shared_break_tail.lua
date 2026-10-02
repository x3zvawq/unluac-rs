-- regress_294_luau_continue_shared_break_tail: if/elseif continue不能抢占while或repeat的共享break tail
-- unluac: expect-contains [[while ]]
-- unluac: expect-contains [[repeat]]
-- unluac: expect-contains [[continue]]
-- unluac: expect-contains [[break]]
-- 循环初始化的数组缓冲保留完整控制区，后继断言不得回退为逐轮增长的 callee 别名。
-- unluac: expect-max-count [[ = assert]] [[0]] [[@variant=O0]]
-- 循环的两个退出使用同一计数状态，不应额外创建跨循环的空结果接棒。
-- unluac: expect-ast-count [[empty-local]] [[0]] [[@proto=0]] [[@variant=O2]]
-- 断言的 Boolean 预写属于完整参数帧，不应以独立旧结果覆盖残留在两次 assert 之间。
-- unluac: expect-max-count [[ = false]] [[0]] [[@variant=O2]]
-- 六段常量调用的状态循环恢复后，原 SUB 与动态 CALL 数量在每轮回编译保持不变。
-- unluac: expect-instruction-count [[sub]] [[7]] [[@proto=0]] [[@variant=O2]]
-- unluac: expect-instruction-count [[call]] [[13]] [[@proto=0]] [[@variant=O2]]
-- 成组结果不引入状态接棒，动态调用直接处在各自断言参数中。
-- unluac: expect-ast-count [[local-binding]] [[17]] [[@proto=0]] [[@variant=O2]]
-- unluac: expect-ast-count [[assign]] [[0]] [[@proto=0]] [[@variant=O2]]
-- unluac: expect-not-contains [[goto ]]
-- unluac: expect-not-contains [[::L]]
-- unluac: expect-not-contains [[unresolved]]
-- unluac: expect-not-contains [[unluac error]]
-- unluac: expect-contains [[<= 0]]
-- unluac: expect-not-contains [[ = 0]]
-- unluac: expect-ast-count [[while]] [[1]] [[@proto=1]]
-- unluac: expect-ast-count [[repeat]] [[1]] [[@proto=2]]
-- unluac: expect-ast-count [[continue]] [[1]] [[@proto=1]]
-- unluac: expect-ast-count [[continue]] [[1]] [[@proto=2]]
-- unluac: expect-ast-count [[break]] [[1]] [[@proto=1]]
-- unluac: expect-ast-count [[break]] [[1]] [[@proto=2]]
-- unluac: expect-ast-count [[local-decl]] [[0]] [[@proto=1]]
-- unluac: expect-ast-count [[local-decl]] [[0]] [[@proto=2]]
local function run_while(a, b, n)
    while n > 0 do
        n -= 1
        if not a then
            print("while-effect", n)
        elseif b then
            continue
        end
        if n == 1 then
            break
        end
    end
    return n
end

local function run_repeat(a, b, n)
    repeat
        n -= 1
        if not a then
            print("repeat-effect", n)
        elseif b then
            continue
        end
        if n == 1 then
            break
        end
    until n <= 0
    return n
end

local w1, w2, w3 = run_while(false, false, 3), run_while(true, true, 3), run_while(true, false, 3)
-- O2 复用 while 状态槽保存 r1；让两次结果不同，后继覆盖不能改变已保存的 w3。
local r1, r2, r3 = run_repeat(false, false, -1), run_repeat(true, true, 3), run_repeat(true, false, 3)
assert(w1 == 1 and w2 == 0 and w3 == 1)
assert(r1 == -2 and r2 == 0 and r3 == 1)
print("regress_294_luau_continue_shared_break_tail", w1, w2, w3, r1, r2, r3)

-- continue 必须跳过 n==1 的 break；repeat 即使初始 n<=0 也执行一轮。
for _, n in ipairs({-1, 0, 1, 2, 4}) do
    for _, a in ipairs({true, false}) do
        for _, b in ipairs({true, false}) do
            local remaining = ((a and b) or n == 1) and 0 or 1
            local expected_while = n <= 0 and n or remaining
            local expected_repeat = n <= 0 and n - 1 or remaining
            print("shared break paths", n, a, b)
            assert(run_while(a, b, n) == expected_while)
            assert(run_repeat(a, b, n) == expected_repeat)
        end
    end
end
