-- regress_244_effectful_errnnil_tbc: ERRNNIL/TBC 都可能在原位置立即抛错
-- unluac: expect-contains [[<close>]]
-- unluac: expect-contains [[global effect_guard = 2]]
-- unluac: expect-ast-count [[function]] [[2]]
-- unluac: expect-ast-count [[close-binding]] [[1]]
-- unluac: expect-ast-max [[if]] [[0]]
-- unluac: expect-ast-max [[local-binding]] [[4]]

local stage = 0
local tbc_ok = pcall(function()
    stage = 1
    local invalid <close> = {}
    stage = 2
end)
assert(not tbc_ok)
assert(stage == 1)

local global_ok = pcall(function()
    stage = 3
    global effect_guard = 1
    stage = 4
    global effect_guard = 2
    stage = 5
end)
assert(not global_ok)
assert(stage == 4)
assert(effect_guard == 1)

print("regress_244_effectful_errnnil_tbc")
