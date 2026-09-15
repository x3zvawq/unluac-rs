-- regress_101_branch_into_loop_header_phi#1: branch 外部臂与 loop backedge 共同拥有 header phi
-- unluac: expect-contains [[if ]]
-- unluac: expect-contains [[repeat]]
-- unluac: expect-not-contains [[goto ]]
-- unluac: expect-not-contains [[::L]]
-- unluac: expect-not-contains [[unresolved]]
-- unluac: expect-not-contains [[unluac error]]
-- unluac: expect-not-contains [[r1_1 = r1_0]]
-- unluac: expect-ast-min [[if]] [[1]] [[@proto=1]]
-- unluac: expect-ast-min [[repeat]] [[1]] [[@proto=1]]
local function run(a, b)
    local x = 0
    if a and b then
        x = x + 1
    end
    repeat
        x = x + 1
    until a
    return x
end

local written, preserved = run(true, true), run(true, false)
assert(written == 2 and preserved == 1)
print("regress_101_branch_into_loop_header_phi#1", written, preserved)
