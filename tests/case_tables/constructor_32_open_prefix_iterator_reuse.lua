-- unluac: expect-not-contains [[table-set-list]]
-- unluac: expect-not-contains [[goto ]]
-- unluac: expect-ast-count [[table-list-field]] [[12]]
-- unluac: expect-ast-count [[generic-for]] [[1]]
local function apply(player)
    local sayings = {
        GetEditorString(32, 1), GetEditorString(32, 2), GetEditorString(32, 3),
        GetEditorString(32, 4), GetEditorString(32, 5), GetEditorString(32, 6),
        GetEditorString(32, 7), GetEditorString(32, 8), GetEditorString(32, 9)
    }
    if #sayings > 0 then player.Talk(sayings[math.random(1, #sayings)]) end
    local remove = { 1, 2, 3 }
    for _, id in ipairs(remove) do
        if player.IsHaveBuff(id, 0) then player.DelBuff(id, 1) end
    end
    return sayings
end

local function check_length(items)
    if #items > 0 then return "positive" end
    return "other"
end
local length_reads = 0
local length_result = 1
local row = setmetatable({}, {
    __len = function()
        length_reads = length_reads + 1
        return length_result
    end,
})
local supports_length = #row == 1
local initial_reads = length_reads
length_result = -1
assert(check_length(row) == "other")
length_result = 0
assert(check_length(row) == "other")
length_result = 2
assert(check_length(row) == (supports_length and "positive" or "other"))
assert(length_reads == initial_reads + (supports_length and 3 or 0))
assert(check_length("") == "other")
assert(check_length("ab") == "positive")
print("length-evaluations", length_reads)

local mode = 0
local events = {}
local function record(value) events[#events + 1] = value end
function GetEditorString(category, id)
    assert(category == 32)
    record("get" .. id)
    if id < 9 then return id, "discard" end
    if mode == 0 then return end
    if mode == 1 then return 9 end
    if mode == 2 then return 9, 10, 11 end
    return 9, nil, 11, nil
end
local spoken = false
local player = {}
function player.Talk(value)
    assert((mode == 3 and value == nil)
        or (type(value) == "number" and value >= 1 and value <= 11))
    record("talk")
    spoken = value
end
function player.IsHaveBuff(id, level)
    assert(level == 0)
    record("has" .. id)
    return id ~= 2
end
function player.DelBuff(id, count)
    assert(count == 1)
    record("del" .. id)
end
local expected = "get1,get2,get3,get4,get5,get6,get7,get8,get9,talk,has1,del1,has2,has3,del3"
for current = 0, 3 do
    mode = current
    events = {}
    spoken = false
    math.randomseed(17)
    local values = apply(player)
    for id = 1, 8 do assert(values[id] == id) end
    if mode == 0 then
        assert(values[9] == nil and values[10] == nil and values[11] == nil)
    elseif mode == 1 then
        assert(values[9] == 9 and values[10] == nil and values[11] == nil)
    elseif mode == 2 then
        assert(values[9] == 9 and values[10] == 10 and values[11] == 11)
    else
        assert(values[9] == 9 and values[10] == nil and values[11] == 11)
    end
    assert(values[12] == nil)
    assert(table.concat(events, ",") == expected)
    print("open-prefix", mode, tostring(spoken), table.concat(events, ","))
end
