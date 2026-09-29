-- regress_88_repeat_degenerate_continue_branch#1: equal branch targets are the repeat tail, not goto
-- unluac: expect-contains [[for ]]
-- unluac: expect-contains [[repeat]]
-- unluac: expect-not-contains [[goto ]]
-- unluac: expect-not-contains [[::L]]
-- unluac: expect-not-contains [[unresolved]]
-- unluac: expect-not-contains [[unluac error]]
-- 等目标边可并入尾部，但原 a 检查仍须保留为空 if。
-- unluac: expect-ast-count [[generic-for]] [[1]] [[@proto=1]]
-- unluac: expect-ast-count [[repeat]] [[1]] [[@proto=1]]
-- unluac: expect-ast-count [[if]] [[2]] [[@proto=1]]
-- unluac: expect-ast-count [[continue]] [[0]] [[@proto=1]]
-- unluac: expect-ast-count [[break]] [[1]] [[@proto=1]]
-- unluac: expect-ast-count [[local-decl]] [[0]] [[@proto=1]]
local function run(a, b, xs)
    local x = 0
    for _ in xs do
        repeat
            if a then
                continue
            end
        until b
        if xs[x] then
            break
        end
    end
    return x
end

local empty_result = run(false, true, {})
local continue_result = run(true, true, { true })
assert(empty_result == 0 and continue_result == 0)
print("regress_88_repeat_degenerate_continue_branch#1", empty_result, continue_result)

for _, n in ipairs({0, 1, 3}) do
    for _, a in ipairs({true, false}) do
        for _, hit in ipairs({true, false}) do
            local reads = 0
            local xs = {}
            for i = 1, n do xs[i] = true end
            setmetatable(xs, {__index = function(_, key)
                reads = reads + 1
                assert(key == 0 and reads <= n)
                return hit
            end})
            assert(run(a, true, xs) == 0)
            assert(reads == ((hit and n > 0) and 1 or n))
            print("degenerate continue paths", n, a, hit, reads)
        end
    end
end
-- b=false 只有空迭代器可终止；非空迭代器会留在原 repeat 中。
assert(run(true, false, {}) == 0)
assert(run(false, false, {}) == 0)
