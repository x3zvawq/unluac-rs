-- regress_101_branch_into_loop_header_phi#1: branch 外部臂与 loop backedge 共同拥有 header phi
-- unluac: expect-contains [[if ]]
-- unluac: expect-contains [[repeat]]
-- unluac: expect-not-contains [[goto ]]
-- unluac: expect-not-contains [[::L]]
-- unluac: expect-not-contains [[unresolved]]
-- unluac: expect-not-contains [[unluac error]]
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

print("regress_101_branch_into_loop_header_phi#1", run(true, true))
