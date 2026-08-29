-- regress_376_unused_initialized_local_suffix: cleanup removes only a dead initialized tail slot
-- unluac: expect-not-contains [[, r0_]]

local function pair()
    return 17, 19
end

local keep, dead = pair()
assert(keep == 17)
