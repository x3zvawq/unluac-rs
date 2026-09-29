-- regress_95_luau_shared_continue_edge_owner#1: indirect continue pad belongs to the outer while
-- unluac: expect-contains [[while ]]
-- unluac: expect-contains [[repeat]]
-- unluac: expect-contains [[for ]]
-- unluac: expect-contains [[continue]]
-- unluac: expect-not-contains [[goto ]]
-- unluac: expect-not-contains [[::L]]
-- unluac: expect-not-contains [[unresolved]]
-- unluac: expect-not-contains [[unluac error]]
-- unluac: expect-not-contains [[r1_2 = r1_1]]
-- unluac: expect-ast-count [[while]] [[1]] [[@proto=1]]
-- unluac: expect-ast-count [[repeat]] [[1]] [[@proto=1]]
-- unluac: expect-ast-count [[numeric-for]] [[1]] [[@proto=1]]
-- unluac: expect-ast-count [[continue]] [[1]] [[@proto=1]]
-- unluac: expect-ast-count [[break]] [[1]] [[@proto=1]]
-- unluac: expect-ast-count [[if]] [[2]] [[@proto=1]]
-- unluac: expect-ast-count [[local-decl]] [[1]] [[@proto=1]]
-- unluac: expect-ast-count [[empty-local]] [[0]]
local function run(a, b, should_break)
    local x = 0
    while not b do
        if a then
            continue
        end
        repeat
            for _ = 1, 3 do
                continue
            end
            x = x + 1
        until b
        if should_break then
            break
        end
    end
    return x
end

local result = run(false, true, false)
assert(result == 0)
print("regress_95_luau_shared_continue_edge_owner#1", result)

-- b 是不变参数：b=false 时 a=true 留在外层 while，a=false 留在 repeat。
-- 有限运行只覆盖 b=true 的四组入口；内部 owner 由上述结构断言独立保护。
for _, a in ipairs({true, false}) do
    for _, should_break in ipairs({true, false}) do
        assert(run(a, true, should_break) == 0)
    end
end
