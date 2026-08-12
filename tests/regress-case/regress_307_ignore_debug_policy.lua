-- regress_307_ignore_debug_policy#1: 保留的 debug section 在 ignore 模式下不得进入命名或注释
-- unluac: expect-not-contains [[debug_secret]]
-- unluac: expect-not-contains [[debug_helper]]
-- unluac: expect-not-contains [[debug_param]]
-- unluac: expect-not-contains [[debug_local]]
-- unluac: expect-not-contains [[-- file:]]
-- unluac: expect-not-contains [[-- line ]]
-- unluac: expect-not-contains [[goto ]]
-- unluac: expect-not-contains [[unluac error]]
local debug_secret = { 2, 4, 6 }

local function debug_helper(debug_param)
    local debug_local = debug_secret[debug_param]
    return debug_local or 0
end

print("regress_307_ignore_debug_policy#1", debug_helper(2))
