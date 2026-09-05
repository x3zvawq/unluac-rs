-- Lookup values retain their future reads across many observing statements.
-- N distinct lookup homes remain readable after N GC observations.
local function hold(t)
local a1 = t[1]
local a2 = t[2]
local a3 = t[3]
local a4 = t[4]
local a5 = t[5]
local a6 = t[6]
local a7 = t[7]
local a8 = t[8]
local a9 = t[9]
local a10 = t[10]
local a11 = t[11]
local a12 = t[12]
local a13 = t[13]
local a14 = t[14]
local a15 = t[15]
local a16 = t[16]
local a17 = t[17]
local a18 = t[18]
local a19 = t[19]
local a20 = t[20]
local a21 = t[21]
local a22 = t[22]
local a23 = t[23]
local a24 = t[24]
local a25 = t[25]
local a26 = t[26]
local a27 = t[27]
local a28 = t[28]
local a29 = t[29]
local a30 = t[30]
local a31 = t[31]
local a32 = t[32]
local a33 = t[33]
local a34 = t[34]
local a35 = t[35]
local a36 = t[36]
local a37 = t[37]
local a38 = t[38]
local a39 = t[39]
local a40 = t[40]
local a41 = t[41]
local a42 = t[42]
local a43 = t[43]
local a44 = t[44]
local a45 = t[45]
local a46 = t[46]
local a47 = t[47]
local a48 = t[48]
local a49 = t[49]
local a50 = t[50]
local a51 = t[51]
local a52 = t[52]
local a53 = t[53]
local a54 = t[54]
local a55 = t[55]
local a56 = t[56]
local a57 = t[57]
local a58 = t[58]
local a59 = t[59]
local a60 = t[60]
local a61 = t[61]
local a62 = t[62]
local a63 = t[63]
local a64 = t[64]
collectgarbage("count")
collectgarbage("count")
collectgarbage("count")
collectgarbage("count")
collectgarbage("count")
collectgarbage("count")
collectgarbage("count")
collectgarbage("count")
collectgarbage("count")
collectgarbage("count")
collectgarbage("count")
collectgarbage("count")
collectgarbage("count")
collectgarbage("count")
collectgarbage("count")
collectgarbage("count")
collectgarbage("count")
collectgarbage("count")
collectgarbage("count")
collectgarbage("count")
collectgarbage("count")
collectgarbage("count")
collectgarbage("count")
collectgarbage("count")
collectgarbage("count")
collectgarbage("count")
collectgarbage("count")
collectgarbage("count")
collectgarbage("count")
collectgarbage("count")
collectgarbage("count")
collectgarbage("count")
collectgarbage("count")
collectgarbage("count")
collectgarbage("count")
collectgarbage("count")
collectgarbage("count")
collectgarbage("count")
collectgarbage("count")
collectgarbage("count")
collectgarbage("count")
collectgarbage("count")
collectgarbage("count")
collectgarbage("count")
collectgarbage("count")
collectgarbage("count")
collectgarbage("count")
collectgarbage("count")
collectgarbage("count")
collectgarbage("count")
collectgarbage("count")
collectgarbage("count")
collectgarbage("count")
collectgarbage("count")
collectgarbage("count")
collectgarbage("count")
collectgarbage("count")
collectgarbage("count")
collectgarbage("count")
collectgarbage("count")
collectgarbage("count")
collectgarbage("count")
collectgarbage("count")
collectgarbage("count")
return a1 + a2 + a3 + a4 + a5 + a6 + a7 + a8 + a9 + a10 + a11 + a12 + a13 + a14 + a15 + a16 + a17 + a18 + a19 + a20 + a21 + a22 + a23 + a24 + a25 + a26 + a27 + a28 + a29 + a30 + a31 + a32 + a33 + a34 + a35 + a36 + a37 + a38 + a39 + a40 + a41 + a42 + a43 + a44 + a45 + a46 + a47 + a48 + a49 + a50 + a51 + a52 + a53 + a54 + a55 + a56 + a57 + a58 + a59 + a60 + a61 + a62 + a63 + a64
end
local values = {}
for i = 1, 64 do values[i] = i end
assert(hold(values) == 2080)

print("regress496", hold(values))
