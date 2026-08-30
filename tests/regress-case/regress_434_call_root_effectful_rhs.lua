-- regress_434_call_root_effectful_rhs: same-home call root 可与后续 effectful RHS 原序融合
-- unluac: expect-contains [[return r0_2() + r0_3()]]
-- unluac: expect-not-contains [[unluac error]]

local events = {}

local mt = {
    __add = function(_, increment)
        events[#events + 1] = "add"
        assert(table.concat(events, ",") == "make,rhs,add")
        return increment + 4
    end,
}

local function make_value()
    events[#events + 1] = "make"
    return setmetatable({}, mt)
end

local function next_increment()
    events[#events + 1] = "rhs"
    return 7
end

local function run()
    local result = make_value()
    result = result + next_increment()
    return result
end

assert(run() == 11)
events = {}

local observed_before_overwrite
local function capture_during_rhs()
    local result = make_value()
    result = result + (function()
        local observe = function()
            return result
        end
        observed_before_overwrite = observe()
        return next_increment()
    end)()
    return result
end

assert(capture_during_rhs() == 11)
assert(getmetatable(observed_before_overwrite) == mt)
print("regress_434_call_root_effectful_rhs", table.concat(events, ","))
