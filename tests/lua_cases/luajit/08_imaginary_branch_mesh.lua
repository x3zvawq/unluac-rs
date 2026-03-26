local samples = { 1i, -2i, 3i, -4i, 5i }
local index = 1
local total = 0ULL
local out = {}

::walk::
if index > #samples then
    print("luajit-imag-branch", table.concat(out, ","), tostring(total))
    return
end

local rendered = tostring(samples[index])
local magnitude = tonumber((rendered:match("(%d+)i$")))

if rendered:find("%-") then
    total = total + magnitude * 2ULL + index
    out[#out + 1] = "n" .. magnitude
else
    total = total + magnitude + 7ULL
    out[#out + 1] = "p" .. magnitude
end

index = index + 1
goto walk
