-- regress_286_luau_continue_bvm_shared_tail: 显式continue与BVM共享tail必须保留各自owner
-- unluac: expect-contains [[for ]]
-- unluac: expect-contains [[while ]]
-- unluac: expect-contains [[continue]]
-- unluac: expect-not-contains [[goto ]]
-- unluac: expect-not-contains [[::L]]
-- unluac: expect-not-contains [[unresolved]]
-- unluac: expect-not-contains [[unluac error]]
-- unluac: expect-not-contains [[local r1_2]]
-- unluac: expect-not-contains [[local r2_2]]
-- unluac: expect-contains [[r1_0 = r1_0 + r1_1]]
-- unluac: expect-contains [[r2_1 = r2_1 + r2_0]]
-- unluac: expect-ast-count [[numeric-for]] [[1]] [[@proto=1]]
-- unluac: expect-ast-count [[while]] [[1]] [[@proto=2]]
-- unluac: expect-ast-count [[if]] [[2]] [[@proto=1]]
-- unluac: expect-ast-count [[if]] [[2]] [[@proto=2]]
-- unluac: expect-ast-count [[continue]] [[1]] [[@proto=1]]
-- unluac: expect-ast-count [[continue]] [[1]] [[@proto=2]]
-- unluac: expect-ast-count [[local-decl]] [[1]] [[@proto=1]]
-- unluac: expect-ast-count [[local-decl]] [[1]] [[@proto=2]]
-- unluac: expect-ast-count [[local-binding]] [[2]] [[@proto=2]]
-- unluac: expect-ast-count [[empty-local]] [[0]]
local function run_numeric(a, c, n)
    local x = 0
    for i = 1, n do
        if a then
            if c then
                continue
            end
        else
            x = x + i
        end
        print()
    end
    return x
end

local function run_while(a, b, c, n)
    local i = 0
    local x = 0
    while i < n do
        i = i + 1
        if a or b then
            if c then
                continue
            end
        else
            x = x + i
        end
        print()
    end
    return x
end

local numeric_fallback = run_numeric(false, true, 2)
local numeric_continue = run_numeric(true, true, 2)
local while_fallback = run_while(false, false, true, 2)
local while_continue = run_while(true, false, true, 2)
assert(numeric_fallback == 3 and numeric_continue == 0)
assert(while_fallback == 3 and while_continue == 0)
print(
    "regress_286_luau_continue_bvm_shared_tail",
    numeric_fallback,
    numeric_continue,
    while_fallback,
    while_continue
)

-- 每组标签后原 print() 的空行也是运行观察：continue 必须跳过共享 tail，
-- a=true,c=false 则不累加但仍执行 tail。零轮和多轮分别覆盖入口与回边。
for _, n in ipairs({0, 1, 3}) do
    for _, a in ipairs({true, false}) do
        for _, c in ipairs({true, false}) do
            print("numeric paths", n, a, c)
            assert(run_numeric(a, c, n) == (a and 0 or n * (n + 1) / 2))
            for _, b in ipairs({true, false}) do
                print("while paths", n, a, b, c)
                assert(run_while(a, b, c, n) == ((a or b) and 0 or n * (n + 1) / 2))
            end
        end
    end
end
