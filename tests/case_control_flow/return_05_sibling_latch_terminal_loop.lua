-- regress_176_sibling_latch_terminal_loop#1: 多个 sibling latch 共同回到 while-true header
-- unluac: expect-not-contains [[goto ]]
-- unluac: expect-not-contains [[::L]]
-- unluac: expect-not-contains [[unluac error]]
-- unluac: expect-contains [[until p1_1 and p1_2]]
-- unluac: expect-contains [[return 1]]
-- unluac: expect-contains [[return 2]]
-- unluac: expect-contains [[return 3]]
-- unluac: expect-ast-count [[repeat]] [[1]]
-- unluac: expect-ast-count [[if]] [[3]]
-- unluac: expect-ast-count [[local-binding]] [[2]]

local function run(a, b, c)
    while true do
        if a then
            if b then
                return 1
            end
        elseif c then
            return 2
        end
        if b and c then
            return 3
        end
    end
end

local result = run(false, false, true)
assert(result == 2)
assert(run(true, true, false) == 1)
assert(run(true, true, true) == 1)
assert(run(false, true, true) == 2)
assert(run(0, "", nil) == 1)
assert(run(nil, 0, "") == 2)
-- 固定参数下第三个返回被前两个分支遮住，但字节码中的检查和返回仍须保留。
print("regress_176_sibling_latch_terminal_loop#1", result)
