-- 单次/重复读取不授权删除返回 COPY 的低槽输入；两项输入共享完整三返回准备区。
-- 同一函数形状的 caller GC 反例由 lifetime/roots_02 的 copied_repeated 覆盖，避免重复观察器。
-- unluac: expect-count [[return r1_0, r1_1, r1_1]] [[1]]
-- unluac: expect-ast-min [[local-decl]] [[1]] [[@proto=1]]
-- unluac: expect-ast-max [[local-decl]] [[2]] [[@proto=1]]

local function run(first, repeated)
    local once = first
    local kept = repeated
    return once, kept, kept
end

local first, second, third = run(3, 4)
assert(first == 3 and second == 4 and third == 4)

-- 重复返回同一对象，且保留 false 和尾部 nil 的值及数量。
local left, right = {}, {}
first, second, third = run(left, right)
assert(first == left and second == right and third == right and first ~= second)
first, second, third = run(false, nil)
assert(first == false and second == nil and third == nil)
assert(select("#", run(false, nil)) == 3)
