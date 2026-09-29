-- regress_265_entry_loop_exit_state#1: entry-header loop must initialize an all-inside exit phi
-- unluac: expect-not-contains [[goto ]]
-- unluac: expect-not-contains [[::L]]
-- unluac: expect-not-contains [[unresolved]]
-- unluac: expect-not-contains [[unluac error]]
-- 编译器将 repeat 的两条出口拆成相邻 while，原 a 检查仍须保留。
-- unluac: expect-ast-count [[while]] [[2]] [[@proto=1]]
-- unluac: expect-ast-count [[if]] [[1]] [[@proto=1]]
-- unluac: expect-ast-count [[local-decl]] [[0]] [[@proto=1]]
local function run(a, b, c)
    repeat
        if b then
            while c do
                c = false
            end
            break
        end
        a = true
    until a
    return c
end

local nested = run(false, true, true)
local direct = run(false, false, true)
assert(nested == false and direct == true)
print("regress_265_entry_loop_exit_state#1a", nested)
print("regress_265_entry_loop_exit_state#1b", direct)

for _, a in ipairs({ false, true }) do
    for _, b in ipairs({ false, true }) do
        for _, c in ipairs({ false, true }) do
            assert(run(a, b, c) == (not b and c))
        end
    end
end
