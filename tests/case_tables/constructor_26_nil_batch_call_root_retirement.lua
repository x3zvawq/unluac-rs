local weak = setmetatable({}, { __mode = "v" })
local events = {}
local function clamp(value, floor)
    collectgarbage("collect")
    events[#events + 1] = tostring(weak[1] ~= nil) .. ":" .. tostring(weak[2] ~= nil)
    return math.max(value, floor)
end
local limit1, limit2 = 100, 70
local key1, key2 = 1, 2
local weight1, weight2, multiplier = 0.6, 0.4, 1
GetGlobalCounterValue = function(key)
    local value = setmetatable({ value = key * 7 }, {
        __sub = function(left, right) return left - right.value end,
    })
    weak[key] = value
    return value
end
local function calculate(self)
    local free = clamp(limit1 - GetGlobalCounterValue(key1), 0)
    local paid = clamp(limit2 - GetGlobalCounterValue(key2), 0)
    local score = ((weight1 * free) + (weight2 * paid)) * multiplier
    local rows = {}
    local unused1, unused2, unused3, unused4
    for index = 1, 1 do
    end
    return score, rows
end
local score, rows = calculate({})
assert(score == 78.2 and next(rows) == nil)
assert(table.concat(events, ",") == "false:false,false:false")
print("callee prefix", table.concat(events, ","))
