-- 相邻 fixed SETLIST 恢复字段/动态索引构造器，保留读取顺序和 nil/false 槽。
-- unluac: expect-not-contains [[unluac error]]
-- unluac: expect-not-contains [[table-set-list]]
-- unluac: expect-ast-count [[table-list-field]] [[5]] [[@proto=1]] [[@dialect=lua5.1]]
-- unluac: expect-ast-count [[table-list-field]] [[2]] [[@proto=2]] [[@dialect=lua5.1]]
local DS = {
    AP = "ap",
    FE = nil,
    LA = "la",
    TA = false,
    SH = "sh",
}

local function build_ids()
    local ids = {
        DS.AP,
        DS.FE,
        DS.LA,
        DS.TA,
        DS.SH,
    }
    return ids[1], ids[2], ids[3], ids[4], ids[5]
end

local ap, fe, la, ta, sh = build_ids()
assert(ap == "ap" and fe == nil and la == "la" and ta == false and sh == "sh")
print("regress_326_adjacent_uncertain_setlist", ap, fe, la, ta, sh)

local function build_indexed()
    local id = getId()
    return {
        D[(id - 16) * 3 + 1],
        D[(id - 16) * 3 + 3],
    }
end

local events = {}
local selected = 17
function getId()
    events[#events + 1] = "id"
    return selected
end
D = setmetatable({}, { __index = function(_, key)
    events[#events + 1] = tostring(key)
    if key == 4 then return nil end
    if key == 6 then return false end
    return key * 10
end })

local first = build_indexed()
assert(first[1] == nil and first[2] == false)
assert(table.concat(events, ",") == "id,4,6")
print("indexed nil/false", first[1], first[2], table.concat(events, ","))

events, selected = {}, 18
local second = build_indexed()
assert(second[1] == 70 and second[2] == 90)
assert(table.concat(events, ",") == "id,7,9")
print("indexed values", second[1], second[2], table.concat(events, ","))
