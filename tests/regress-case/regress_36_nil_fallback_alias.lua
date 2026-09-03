-- unluac: expect-contains [[ == nil then]]
-- unluac: expect-contains [[ = env]]
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

assert(b == env)
assert(b.one() == b and b.two() == b.one)
return b.two
