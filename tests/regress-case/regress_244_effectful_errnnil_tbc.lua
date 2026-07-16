-- regress_244_effectful_errnnil_tbc: ERRNNIL/TBC 都可能在原位置立即抛错
-- unluac: expect-contains [[<close>]]
-- unluac: expect-contains [[global effect_guard = 2]]

local tbc_ok = pcall(function()
    local invalid <close> = {}
end)
assert(not tbc_ok)

local global_ok = pcall(function()
    global effect_guard = 1
    global effect_guard = 2
end)
assert(not global_ok)

print("regress_244_effectful_errnnil_tbc")
