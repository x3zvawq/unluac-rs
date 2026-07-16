-- regress_224_table_capture_writeback#1: table 构造折叠不能先于捕获槽位写回恢复
-- unluac: expect-not-contains [[unluac error]]
local function run()
    local value = "old"
    local read = function()
        return value
    end
    local result = {}
    value = "new"
    result[1] = value
    return read(), result[1]
end

local captured, field = run()
assert(captured == "new")
assert(field == "new")
print("regress_224_table_capture_writeback#1", captured, field)
