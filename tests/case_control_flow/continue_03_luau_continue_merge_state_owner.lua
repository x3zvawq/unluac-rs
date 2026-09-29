-- regress_112_luau_continue_merge_state_owner#1: continue merge pad 保留嵌套 loop state owner
-- unluac: expect-contains [[while ]]
-- unluac: expect-contains [[repeat]]
-- unluac: expect-contains [[continue]]
-- unluac: expect-not-contains [[goto ]]
-- unluac: expect-not-contains [[::L]]
-- unluac: expect-not-contains [[unresolved]]
-- unluac: expect-not-contains [[unluac error]]
-- unluac: expect-not-contains [[while false do]]
-- unluac: expect-contains [[in p1_3 do]]
-- unluac: expect-ast-count [[repeat]] [[2]] [[@proto=1]]
-- unluac: expect-ast-count [[while]] [[2]] [[@proto=1]]
-- O2 编译器已消除立即 break 的 numeric-for；其它优化级别保留原循环。
-- unluac: expect-ast-count [[numeric-for]] [[1]] [[@proto=1]] [[@variant=O0]]
-- unluac: expect-ast-count [[numeric-for]] [[1]] [[@proto=1]] [[@variant=O1]]
-- unluac: expect-ast-count [[numeric-for]] [[0]] [[@proto=1]] [[@variant=O2]]
-- unluac: expect-ast-count [[generic-for]] [[2]] [[@proto=1]]
-- unluac: expect-ast-count [[do-block]] [[0]] [[@proto=1]]
-- 循环状态和已有 for 绑定之外，不再为每层结果合流制造独立的暂存声明。
-- unluac: expect-ast-count [[local-binding]] [[11]] [[@proto=1]] [[@variant=O0]]
-- unluac: expect-ast-count [[local-binding]] [[11]] [[@proto=1]] [[@variant=O1]]
-- unluac: expect-ast-count [[local-binding]] [[10]] [[@proto=1]] [[@variant=O2]]
-- unluac: expect-ast-count [[empty-local]] [[0]] [[@proto=1]]
-- until 的索引检查和次数上界保持在同一个尾条件中。
-- unluac: expect-contains [[until p1_3[]]
local function run(a, b, c, xs)
    local x = 0
    local while_rounds, while_tails, repeat_rounds, inner_rounds = 0, 0, 0, 0
    while not b and while_rounds < 2 do
        while_rounds = while_rounds + 1
        if a then
            if xs[x] then
                print(x)
            end
            if a and b then
                break
            end
            while b do
                if a or c then
                    continue
                else
                    x = x + 1
                    x = x + 1
                end
            end
        else
            for i = 1, 3 do
                break
            end
            continue
        end
        if xs[x] then
            break
        end
        while_tails = while_tails + 1
        while not b do
            for k, v in xs do
                print(x)
                if xs[x] then
                    break
                end
            end
            break
        end
    end
    repeat
        repeat_rounds = repeat_rounds + 1
        if a then
            continue
        end
        local steps = 0
        repeat
            steps = steps + 1
            inner_rounds = inner_rounds + 1
            if a or c then
                if a and b then
                    x = x + 1
                end
                for k, v in xs do
                    x = x + 1
                    x = x + 1
                end
                continue
            else
                if a or c then
                    print(x)
                else
                    break
                end
            end
        until xs[x] or steps == 2
    until a or c or repeat_rounds == 2
    return x, while_rounds, while_tails, repeat_rounds, inner_rounds
end

-- 正常退出的尾部定义必须先于结果合流；提前 break 则绕过这份 tail。
local normal = run(true, true, false, {})
local early = run(true, false, false, {[0] = true})
assert(normal == 0 and early == 0)
print("regress_112_luau_continue_merge_state_owner#1", normal, early)

-- 有限边界放在 continue 之前；所有 a/b/c 与索引结果组合都实际执行。
-- 内层 while b 处于 while not b 内，对稳定参数不可达，仍保留原指令结构。
for mask = 0, 7 do
    local a = mask % 2 == 1
    local b = math.floor(mask / 2) % 2 == 1
    local c = mask >= 4
    for hit_flag = 0, 1 do
        local hit = hit_flag == 1
        local reads = 0
        local xs = setmetatable({10, 20}, {__index = function(_, key)
            assert(key == 0 or key == 4 or key == 8)
            reads = reads + 1
            return hit
        end})
        local x, wr, wt, rr, ir = run(a, b, c, xs)
        local want_wr = b and 0 or (a and hit and 1 or 2)
        local want_wt = (not b and a and not hit) and 2 or 0
        local want_rr = (a or c) and 1 or 2
        local want_ir = a and 0 or (c and (hit and 1 or 2) or 2)
        local want_x = (not a and c) and want_ir * 4 or 0
        local want_reads = (not b and a) and (hit and 2 or 8) or 0
        if not a and c then
            want_reads = want_reads + want_ir
        end
        assert(x == want_x and wr == want_wr and wt == want_wt)
        assert(rr == want_rr and ir == want_ir and reads == want_reads)
        print("continue merge owners", mask, hit_flag, x, wr, wt, rr, ir, reads)
    end
end
