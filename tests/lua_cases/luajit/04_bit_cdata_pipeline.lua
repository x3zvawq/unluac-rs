local bit = require("bit")

local stages = { 0x21ULL, 0x34ULL, 0x55ULL, 0x89ULL, 0x144ULL }
local acc = 0x10ULL
local text = {}

for i = 1, #stages do
    local mixed = bit.bxor(tonumber(acc % 0xffULL), tonumber(stages[i] % 0xffULL))

    if mixed % 2 == 0 then
        acc = acc + mixed + i
    else
        acc = acc * 2ULL - mixed
    end

    text[#text + 1] = string.format("%02x", mixed)
end

print("luajit-bit", table.concat(text, ":"), tostring(acc))
