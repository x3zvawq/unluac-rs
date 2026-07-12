-- regress_72_loop_exit_generic_owner#1: loop-owned exit phi suppresses its generic candidate
-- unluac: expect-contains [[while r0_0 < 2 do]]
-- unluac: expect-contains [[return r0_0]]
-- unluac: expect-not-contains [[unresolved]]
-- unluac: expect-not-contains [[unluac error]]

local result = 0
while result < 2 do
    result = result + 1
    if result > 3 then
        break
    end
end
return result
