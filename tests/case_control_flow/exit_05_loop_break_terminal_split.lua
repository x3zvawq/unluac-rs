-- regress_89_loop_break_terminal_split#1: break exit may split into post-loop and duplicated return
-- unluac: expect-ast-count [[while]] [[1]] [[@proto=1]]
-- unluac: expect-ast-count [[generic-for]] [[1]] [[@proto=1]]
-- unluac: expect-ast-count [[break]] [[2]] [[@proto=1]]
-- unluac: expect-ast-count [[if]] [[3]] [[@proto=1]]
-- unluac: expect-ast-count [[local-decl]] [[1]] [[@proto=1]]
-- unluac: expect-not-contains [[goto ]]
-- unluac: expect-not-contains [[::L]]
-- unluac: expect-not-contains [[unresolved]]
-- unluac: expect-not-contains [[unluac error]]
local function run(a, b, xs)
    local x = 0
    for _ in xs do
        if xs[x] then
            break
        end
    end
    while not b do
        if a then
            if xs[x] then
                break
            end
            break
        end
        x = x + 1
    end
    return x
end

local loop_break = run(true, false, { [0] = true })
local branch_break = run(true, false, {})
local skipped_while = run(false, true, { true })
assert(loop_break == 0 and branch_break == 0 and skipped_while == 0)
print("regress_89_loop_break_terminal_split#1", loop_break, branch_break, skipped_while)

-- a=false,b=false 时 while 不终止；其余 Boolean 路径按第一个循环是否提前退出计数。
for _, mode in ipairs({
    { true, false, true, 2 }, { true, false, false, 3 },
    { true, true, true, 1 }, { true, true, false, 2 },
    { false, true, true, 1 }, { false, true, false, 2 },
}) do
    local reads = 0
    local xs = setmetatable({ 1, 2 }, {
        __index = function(_, key)
            assert(key == 0)
            reads = reads + 1
            return mode[3]
        end,
    })
    assert(run(mode[1], mode[2], xs) == 0)
    assert(reads == mode[4])
end
