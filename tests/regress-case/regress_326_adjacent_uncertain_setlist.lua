-- regress_326_adjacent_uncertain_setlist: 带 debug local 的相邻 fixed SETLIST 应恢复为原构造器
-- unluac: expect-not-contains [[unluac error]]
-- unluac: expect-not-contains [[table-set-list]]
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

print("regress_326_adjacent_uncertain_setlist", build_ids())
