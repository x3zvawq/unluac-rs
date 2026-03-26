local coeffs = { 0x1.8p+1, 0x1.2p+0, -0x1.0p-1, 0x1.4p-2 }
local acc = 0x1p+0
local parts = {}

for i = 1, #coeffs do
    acc = acc * coeffs[i] + (i / 3)
    parts[#parts + 1] = string.format("%.6f", acc)
end

print("luajit-hexfloat", table.concat(parts, ","), string.format("%.6f", acc))
