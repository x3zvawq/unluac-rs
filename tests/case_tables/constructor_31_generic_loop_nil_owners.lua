-- unluac: expect-not-contains [[table-set-list]]
-- unluac: expect-not-contains [[goto ]]
-- unluac: expect-ast-count [[table-list-field]] [[2]] [[@proto=1]] [[@dialect=lua5.1]]
-- unluac: expect-ast-count [[generic-for]] [[1]]
-- unluac: expect-contains [[local npc, unused, endtime]] [[@debug=retained]] [[@dialect=lua5.1]]
local function collect(actor, items)
    local entries = {}
    local npc, unused, endtime
    for _, item in Traverse(items) do
        local buff = actor.GetBuff(item.SignBuffID, 0)
        if buff then
            endtime = buff.GetEndTime()
            npc = GetNpc(buff.nCustomValue)
            if npc then
                if endtime then
                    table.insert(entries, { npc, endtime })
                end
            end
        end
    end
    return entries
end

local events = {}
local function record(value) events[#events + 1] = value end
function Traverse(items)
    local index = 0
    return function()
        index = index + 1
        record("next" .. index)
        if items[index] then return index, { SignBuffID = items[index] } end
    end
end
local first, second = {}, {}
function GetNpc(id)
    record("npc" .. id)
    if id == 3 then return nil end
    if id == 8 then return false end
    if id == 5 or id == 7 then return second end
    return first
end
local buff = { nCustomValue = 0 }
function buff.GetEndTime()
    local id = buff.nCustomValue
    record("time" .. id)
    if id == 4 then return nil end
    if id == 5 then return false end
    if id == 6 then return 0 end
    if id == 7 then return 11 end
    if id == 9 then return 21 end
    return 13
end
local actor = {}
function actor.GetBuff(id, level)
    assert(level == 0)
    record("buff" .. id)
    if id == 1 then return nil end
    if id == 2 then return false end
    buff.nCustomValue = id
    return buff
end
local rows = collect(actor, { 1, 2, 3, 4, 5, 6, 7, 8, 9 })
assert(#rows == 3)
assert(rows[1] ~= rows[3])
assert(rows[1][1] == first)
assert(rows[1][2] == 0)
assert(rows[1][3] == nil)
assert(rows[2][1] == second)
assert(rows[2][2] == 11)
assert(rows[2][3] == nil)
assert(rows[3][1] == first)
assert(rows[3][2] == 21)
assert(rows[3][3] == nil)
local expected = "next1,buff1,next2,buff2,next3,buff3,time3,npc3"
    .. ",next4,buff4,time4,npc4,next5,buff5,time5,npc5"
    .. ",next6,buff6,time6,npc6,next7,buff7,time7,npc7"
    .. ",next8,buff8,time8,npc8,next9,buff9,time9,npc9,next10"
assert(table.concat(events, ",") == expected)
print("generic-nil-owners", expected)
events = {}
assert(next(collect(actor, {})) == nil)
assert(table.concat(events, ",") == "next1")
events = {}
local skipped_rows = collect(actor, { 1, 4 })
assert(next(skipped_rows) == nil)
assert(table.concat(events, ",") == "next1,buff1,next2,buff4,time4,npc4,next3")
print("generic-nil-skips", table.concat(events, ","))
