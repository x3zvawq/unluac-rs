-- regress_287_luau_continue_nested_loop_tail: continue前的嵌套loop tail必须由外层branch共享
-- unluac: expect-contains [[continue]]
-- unluac: expect-contains [[for ]]
-- unluac: expect-not-contains [[goto ]]
-- unluac: expect-not-contains [[::L]]
-- unluac: expect-not-contains [[unresolved]]
-- unluac: expect-not-contains [[unluac error]]
-- unluac: expect-contains [[r1_0 = r1_0 + r1_2]]
-- unluac: expect-ast-count [[numeric-for]] [[2]] [[@proto=1]]
-- unluac: expect-ast-count [[if]] [[2]] [[@proto=1]]
-- unluac: expect-ast-count [[continue]] [[1]] [[@proto=1]]
-- unluac: expect-ast-count [[local-decl]] [[1]] [[@proto=1]]
-- unluac: expect-ast-count [[empty-local]] [[0]]
local function run(a, c, n, inner_n)
    local x = 0
    for i = 1, n do
        if a then
            if c then
                continue
            end
        else
            x = x + i
        end
        for j = 1, inner_n do
            x = x + j
        end
    end
    return x
end

local fallback = run(false, false, 3, 2)
local no_inner = run(false, false, 3, 0)
local selected = run(true, false, 3, 2)
local continued = run(true, true, 3, 2)
assert(fallback == 15 and no_inner == 6 and selected == 9 and continued == 0)
print(
    "regress_287_luau_continue_nested_loop_tail",
    fallback,
    no_inner,
    selected,
    continued
)

-- 分别改变两层循环的次数，避免遗漏 continue 跳过整个内层循环的路径。
for _, n in ipairs({0, 1, 3}) do
    for _, inner_n in ipairs({0, 1, 2}) do
        for _, a in ipairs({true, false}) do
            for _, c in ipairs({true, false}) do
                local outer_sum = a and 0 or n * (n + 1) / 2
                local inner_sum = (a and c) and 0 or n * inner_n * (inner_n + 1) / 2
                local result = run(a, c, n, inner_n)
                assert(result == outer_sum + inner_sum)
                print("nested continue paths", n, inner_n, a, c, result)
            end
        end
    end
end
