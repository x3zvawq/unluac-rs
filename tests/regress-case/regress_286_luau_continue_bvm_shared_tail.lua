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

print(
    "regress_286_luau_continue_bvm_shared_tail",
    run_numeric(false, true, 2),
    run_numeric(true, true, 2),
    run_while(false, false, true, 2),
    run_while(true, false, true, 2)
)
