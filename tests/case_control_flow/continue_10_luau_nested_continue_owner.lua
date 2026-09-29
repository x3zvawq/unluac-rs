-- regress_349_luau_nested_continue_owner: nested continue belongs to the inner loop and must not block folding the outer repeat tail
-- unluac: expect-contains [[until not p1_1 and p1_2 or p1_3]]
-- 内层 continue 可恢复为跳过本轮输出的条件；仍须保留筛选条件且不能阻止外层尾条件合并。
-- unluac: expect-contains [[if not p1_0 or r1_0 ~= 2 then]]
-- unluac: expect-not-contains [[if p1_1 then]]
-- unluac: expect-not-contains [[if p1_2 then]]
-- unluac: expect-contains [[if not p2_1 then]]
-- unluac: expect-not-contains [[until true]]
-- unluac: expect-ast-count [[repeat]] [[1]] [[@proto=1]]
-- unluac: expect-ast-count [[numeric-for]] [[1]] [[@proto=1]]
-- unluac: expect-ast-count [[if]] [[1]] [[@proto=1]]
-- unluac: expect-ast-count [[continue]] [[0]] [[@proto=1]]
-- unluac: expect-ast-count [[local-decl]] [[0]] [[@proto=1]]
-- unluac: expect-ast-count [[repeat]] [[0]] [[@proto=2]]
-- unluac: expect-ast-count [[numeric-for]] [[1]] [[@proto=2]]
-- unluac: expect-ast-count [[if]] [[2]] [[@proto=2]]
-- unluac: expect-ast-count [[local-decl]] [[0]] [[@proto=2]]
-- unluac: expect-ast-count [[numeric-for]] [[1]] [[@proto=3]]
-- unluac: expect-ast-count [[repeat]] [[0]] [[@proto=3]]
-- unluac: expect-ast-count [[local-decl]] [[1]] [[@proto=3]]
-- unluac: expect-not-contains [[goto ]]
-- unluac: expect-not-contains [[unresolved]]
local function run(skip_inner, skip_outer, stop, latch)
    repeat
        for index = 1, 3 do
            if skip_inner and index == 2 then
                continue
            end
            print("visit", index)
        end
        if skip_outer then
            continue
        end
        if stop then
            break
        end
    until latch
    return "done"
end

assert(run(true, true, false, true) == "done")
assert(run(false, false, true, false) == "done")
assert(run(false, false, false, true) == "done")

local function run_single_pass(skip_inner, stop)
    repeat
        for index = 1, 3 do
            if skip_inner and index == 2 then
                continue
            end
            print("single-visit", index)
        end
        if stop then
            break
        end
        print("single-tail")
    until true
    return "single-done"
end

assert(run_single_pass(true, true) == "single-done")
assert(run_single_pass(false, false) == "single-done")

-- 与下面 generic-for 中的筛选使用同一个短路形状，观察 numeric-for 的
-- 非尾部回边；跳过条件最后一项会错误增加 visits。
local function numeric_visits(a, b, c)
    local visits = 0
    for index = 1, 2 do
        if a or (not b and c) then
            visits = visits + 1
        end
    end
    return visits
end

-- 参数在循环中不变；只执行可退出组合，逐组输出检查内层 index=2 的筛选。
-- latch=false 且 (skip_outer=true 或 stop=false) 原本不终止。
for _, skip_inner in ipairs({true, false}) do
    for _, skip_outer in ipairs({true, false}) do
        for _, stop in ipairs({true, false}) do
            for _, latch in ipairs({true, false}) do
                local expected_visits = latch and 2 or ((not skip_outer and stop) and 2 or 0)
                assert(numeric_visits(latch, skip_outer, stop) == expected_visits)
                if latch or (not skip_outer and stop) then
                    print("nested owner paths", skip_inner, skip_outer, stop, latch)
                    assert(run(skip_inner, skip_outer, stop, latch) == "done")
                end
            end
        end
    end
    for _, stop in ipairs({true, false}) do
        print("single pass paths", skip_inner, stop)
        assert(run_single_pass(skip_inner, stop) == "single-done")
    end
end
