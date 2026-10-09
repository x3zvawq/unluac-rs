-- unluac: expect-not-contains [[table-set-list]]
-- unluac: expect-ast-count [[table-list-field]] [[12]] [[@proto=2]] [[@dialect=lua5.1]]
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
    -- 独立索引写的 RHS 在槽 9 开始；最后一次发布后，后继 CALL 复用该入口。
    result[3] = { 11, 12, 13, 14 }
    result[4] = { 21, 22, 23, 24 }
    local amount = self.GetItemAmount(5, 6)
    return result, amount
end
local result, amount = prepare({ GetItemAmount = function(kind, id)
    events[#events + 1] = kind
    events[#events + 1] = id
    return kind * 10 + id
end })
assert(table.concat(result[1], ",") == "21,3,2,1")
assert(table.concat(result[2], ",") == "28,2,1,1")
assert(table.concat(result[3], ",") == "11,12,13,14")
assert(table.concat(result[4], ",") == "21,22,23,24")
assert(amount == 56)
assert(table.concat(events, ",") == "1,2,3,4,5,6")
print("indexed-suffix", amount, table.concat(result[4], ","), table.concat(events, ","))
