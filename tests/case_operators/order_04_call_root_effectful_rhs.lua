-- regress_434_call_root_effectful_rhs: same-home call root 可与后续 effectful RHS 原序融合
-- 捕获旧值的 IIFE 仍应保留在原 RHS，不额外生成具名 callee/result 临时变量。

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
assert(table.concat(events, ",") == "make,rhs,add")
events = {}
assert(select("#", run()) == 1)
assert(table.concat(events, ",") == "make,rhs,add")
events = {}
assert(select("#", capture_during_rhs()) == 1)
assert(getmetatable(observed_before_overwrite) == mt)
print("regress_434_call_root_effectful_rhs", table.concat(events, ","))

-- PUC 原 ADD 直接读取 captured local；RHS 写入后必须读取新值，不能伪造调用前快照。
local function capture_write_rhs()
    local result = 3
    result = result + (function()
        result = 10
        return 2
    end)()
    return result
end
assert(capture_write_rhs() == 12)
