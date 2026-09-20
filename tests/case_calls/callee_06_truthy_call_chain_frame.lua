-- unluac: expect-ast-count [[local-decl]] [[0]] [[@proto=1]] [[@dialect=lua5.1]]
-- unluac: expect-ast-count [[local-decl]] [[0]] [[@proto=1]] [[@dialect=lua5.4]]
-- unluac: expect-contains [[local active =]] [[@debug=retained]]
-- 条件链保留 load、字段读取、active 调用的次数与顺序，包括 false/nil 和 truthy 结果。
local function enabled(load)
    if load("event").active() then
        return 1
    end
    return 0
end

local trace = {}
local result
local function load(name)
    trace[#trace + 1] = name
    return setmetatable({}, {
        __index = function(_, key)
            trace[#trace + 1] = key
            return function()
                trace[#trace + 1] = "call"
                return result, "discarded"
            end
        end,
    })
end
for _, value in ipairs({false, true, 0, ""}) do
    result = value
    assert(enabled(load) == (value and 1 or 0))
end
result = nil
assert(enabled(load) == 0)
assert(table.concat(trace, ",") ==
    "event,active,call,event,active,call,event,active,call,event,active,call,event,active,call")

-- 有 debug 身份或后续读取的结果不能与仅用于条件的匿名 scratch 混同。
local function named(load)
    local active = load("named").active()
    if active then return active end
    return active, "fallback"
end
result = false
local first, second = named(load)
assert(first == false and second == "fallback")
print("condition frames", table.concat(trace, ","))
