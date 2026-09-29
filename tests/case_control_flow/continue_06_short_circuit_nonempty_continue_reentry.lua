-- regress_268_short_circuit_nonempty_continue_reentry: 非空continue target下，multi-node短路不能回退成会重入consumed header的plain if/else
-- unluac: expect-not-contains [[goto ]]
-- unluac: expect-not-contains [[::L]]
-- unluac: expect-not-contains [[    continue]]
-- unluac: expect-not-contains [[unluac error]]
-- 原始参数从不更新；保留循环内虽不可达为真的检查，不能按外层路径删掉。
-- unluac: expect-contains [[while not p1_0 do]]
-- unluac: expect-contains [[if (p1_1 or p1_2) and p1_0 then]]
-- unluac: expect-ast-count [[while]] [[1]] [[@proto=1]]
-- unluac: expect-ast-count [[if]] [[1]] [[@proto=1]]
-- unluac: expect-ast-count [[continue]] [[0]] [[@proto=1]]
-- unluac: expect-ast-count [[local-decl]] [[0]] [[@proto=1]]
local function run(a, b, c)
    while true do
        if a then
            break
        elseif (b or c) and a then
            print("x")
        end
    end
end

assert(run(true, false, false) == nil)
-- a=false 原本不终止；有限运行覆盖 a=true 时 b/c 的全部组合。
for _, b in ipairs({true, false}) do
    for _, c in ipairs({true, false}) do
        assert(run(true, b, c) == nil)
    end
end
print("regress_268_short_circuit_nonempty_continue_reentry", type(run))
