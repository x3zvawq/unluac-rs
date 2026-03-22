local function crazy_table_init()
    local t = {
        1,
        2,
        3,
        a = 4,
        [5] = 6,
        7,
        8,
        f = function()
            return 9
        end,
        string.byte("A"),
    }

    return t
end

local t = crazy_table_init()
print("crazy-table", t[1], t[2], t[3], t[4], t[5], t[6], t.a, t.f())
