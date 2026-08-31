-- regress_327_adjacent_open_setlist: 相邻 open SETLIST 保留 vararg 截断、展开与 owner capture
-- unluac: expect-contains [[{ ..., "barrier", ... }]]
-- unluac: expect-not-contains [[unluac error]]
-- unluac: expect-not-contains [[table-set-list]]
local function build(...)
    local values = { ..., "barrier", ... }
    return function()
        return table.concat(values, ",")
    end
end

local read = build("x", "y")
print("regress_327_adjacent_open_setlist", read())
