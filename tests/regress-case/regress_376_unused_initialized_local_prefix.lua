-- regress_376_unused_initialized_local_prefix: cleanup must not shift a live slot's return value
-- unluac: expect-contains [[, r0_]]

local function pair()
    return 17, 19
end

local dead, keep = pair()
assert(keep == 19)
