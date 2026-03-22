local suffix = "tail"
local key = "slot_" .. suffix

local t = {
    list = {
        10,
        20,
        30,
    },
    meta = {
        [key] = 7,
    },
}

t.list[2] = t.list[1] + t.meta[key]
t.meta[key] = t.list[3] - t.list[2]

print("table-dyn", t.list[1], t.list[2], t.list[3], t.meta[key], t.meta.slot_tail)
