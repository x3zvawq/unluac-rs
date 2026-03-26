local ffi = require("ffi")

ffi.cdef([[
typedef struct {
    int id;
    double weight;
} item_t;
]])

local items = ffi.new("item_t[4]")
local weight_sum = 0.0

for i = 0, 3 do
    items[i].id = i + 1
    items[i].weight = (i + 1) * 1.25
    weight_sum = weight_sum + items[i].weight
end

local index = 0
local checksum = 0ULL

::scan::
if index >= 4 then
    print("luajit-ffi-struct", tostring(checksum), string.format("%.2f", weight_sum))
    return
end

local item = items[index]
checksum = checksum + item.id * 3ULL + index + 1ULL
index = index + 1
goto scan
