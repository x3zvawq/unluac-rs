-- regress_150_luau_numeric_for_branch_owner#1: numeric-for 内 continue/break 分支保持互斥 owner
-- unluac: expect-contains [[for ]]
-- unluac: expect-contains [[continue]]
-- unluac: expect-contains [[break]]
-- unluac: expect-not-contains [[goto ]]
-- unluac: expect-not-contains [[::L]]
-- unluac: expect-not-contains [[unresolved]]
-- unluac: expect-not-contains [[unluac error]]
local x = 0
for i = 1, 5 do
    if i < 3 then
        if i == 2 then
            x += 2
            continue
        end
    elseif i == 4 then
        break
    else
        x += 5
    end
    x += 1
end
print(x)
