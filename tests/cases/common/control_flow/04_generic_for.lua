local colors = { "red", "green", "blue" }
local parts = {}

for index, value in ipairs(colors) do
    parts[#parts + 1] = index .. ":" .. value
end

print("gfor", table.concat(parts, "|"))
