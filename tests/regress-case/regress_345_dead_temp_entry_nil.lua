-- regress_345_dead_temp_entry_nil: dead-temp may delete a root-prefix entry-nil primitive write.
-- unluac: expect-not-contains [[local r0_0 = false]]

local discarded = false

local function run()
    return "ok"
end

assert(run() == "ok")
print("regress_345_dead_temp_entry_nil", run())
