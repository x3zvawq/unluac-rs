-- regress_149_lua51_single_arm_nested_generic_for#1: 单臂分支内的 generic-for 保留完整 loop owner
-- unluac: expect-contains [[while ]]
-- unluac: expect-contains [[for ]]
-- unluac: expect-not-contains [[goto ]]
-- unluac: expect-not-contains [[::L]]
-- unluac: expect-not-contains [[unresolved]]
-- unluac: expect-not-contains [[unluac error]]
local function iter(_, i)
    i = i + 1
    if i <= 2 then
        return i
    end
end

local n = 0
while n < 3 do
    n = n + 1
    if n == 2 then
        for _ in iter, nil, 0 do
        end
    end
end
print("done", n)
