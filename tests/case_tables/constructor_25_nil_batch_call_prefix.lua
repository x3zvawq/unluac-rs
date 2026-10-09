-- unluac: expect-not-contains [[table-set-list]]
-- unluac: expect-ast-count [[table-list-field]] [[4]] [[@proto=2]] [[@dialect=lua5.1]]
local max = math.max
local ceil = math.ceil
local limit1, limit2 = 100, 70
local key1, key2 = 1, 2
local weight1, weight2, multiplier = 0.6, 0.4, 1
local fraction1, fraction2, fraction3 = 0.6, 0.3, 0.1
local ids = { { nCounterID = 3 }, { nCounterID = 4 } }
local events = {}
GetGlobalCounterValue = function(key)
    events[#events + 1] = key
    return key * 7
end

-- 后面的 LOADNIL 仍属已知准备区，不能让第二个完整 CALL 失去原帧边界。
local function prepare(self)
    local free = max(limit1 - GetGlobalCounterValue(key1), 0)
    local paid = max(limit2 - GetGlobalCounterValue(key2), 0)
    local score = ((weight1 * free) + (weight2 * paid)) * multiplier
    local result = {}
    local count, first, second, third
    for index = 1, #ids do
        count = max(GetGlobalCounterValue(ids[index].nCounterID), 1)
        first = ceil(score * fraction1 / count)
        second = ceil(score * fraction2 / count)
        third = ceil(score * fraction3 / count)
        result[index] = { count, first, second, third }
    end
    return result
end
local result = prepare({})
assert(table.concat(result[1], ",") == "21,3,2,1")
assert(table.concat(result[2], ",") == "28,2,1,1")
assert(table.concat(events, ",") == "1,2,3,4")
print("prefix", table.concat(result[1], ","), table.concat(result[2], ","), table.concat(events, ","))
