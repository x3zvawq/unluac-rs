-- unluac: expect-contains [[if r0_0 == nil then]]
-- unluac: expect-contains [[r0_0 = env]]
-- unluac: expect-not-contains [[else]]
-- unluac: expect-not-contains [[ or ]]

env = {}

local a = this
local b
if a == nil then
    b = env
else
    b = a
end

function b.one()
    return b
end
function b.two()
    return b.one
end

return b.two
