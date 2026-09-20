-- unluac: expect-ast-count [[local-decl]] [[1]] [[@proto=1]] [[@dialect=lua5.1]] [[@debug=retained]]
-- unluac: expect-ast-count [[local-decl]] [[1]] [[@proto=1]] [[@dialect=lua5.4]] [[@debug=retained]]
-- unluac: expect-contains [[local cd =]] [[@debug=retained]]
-- 左侧算术可能调用元方法，必须先完成它，再调用 clock，最后执行减法。
local function remaining(act_data, event, clock, total_seconds)
    local cd = act_data.cd + event.pull_time - clock()
    cd = cd < 0 and 0 or cd
    if total_seconds < cd then cd = total_seconds end
    return cd
end

local trace = {}
local value = 20
local left = setmetatable({}, {
    __add = function(_, rhs)
        trace[#trace + 1] = "add:" .. rhs
        return value + rhs
    end,
})
local act = setmetatable({}, {
    __index = function(_, key)
        trace[#trace + 1] = key
        return left
    end,
})
local event = setmetatable({}, {
    __index = function(_, key)
        trace[#trace + 1] = key
        return 3
    end,
})
local function clock()
    trace[#trace + 1] = "clock"
    return 10, "discarded"
end
assert(remaining(act, event, clock, 5) == 5)
value = 10
assert(remaining(act, event, clock, 5) == 3)
value = 1
assert(remaining(act, event, clock, 5) == 0)
assert(table.concat(trace, ",") ==
    "cd,pull_time,add:3,clock,cd,pull_time,add:3,clock,cd,pull_time,add:3,clock")
print("arithmetic frames", table.concat(trace, ","))
