local jit = require("jit")

local flags = { jit.status() }
local scale = 0x1.0p+2
local acc = 0x1.0p-4

for i = 1, 8 do
    local factor = (i % 2 == 0) and 0x1.8p-1 or -0x1.4p-2
    acc = acc * scale + factor
    scale = scale + 0x1.0p-3
end

local text = {}

for i = 1, math.min(#flags, 4) do
    text[i] = tostring(flags[i])
end

print("luajit-jit", table.concat(text, ","), string.format("%.6f", acc))
