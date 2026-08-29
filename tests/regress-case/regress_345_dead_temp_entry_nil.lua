-- regress_345_dead_temp_entry_nil: dead-temp may delete root entry-nil primitive writes,
-- including a root sibling after a closed structured loop.
-- unluac: expect-not-contains [[local r0_0 = false]]
-- unluac: expect-not-contains [[local r1_0 = false]]

local discarded = false

local function after_while(flag)
    while flag do
        flag = false
    end
    local discarded_after_loop = false
    print("after-loop")
    return flag
end

local function run()
    return "ok"
end

assert(after_while(true) == false)
assert(after_while(false) == false)
assert(run() == "ok")
print("regress_345_dead_temp_entry_nil", run())
