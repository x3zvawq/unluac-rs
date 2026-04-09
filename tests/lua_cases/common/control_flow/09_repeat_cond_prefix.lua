local t = {}
local i = 0

repeat
    i = i + 1
    t[i] = i * i
until t[i] >= 9

print("repeat-cond-prefix", i, t[1], t[2], t[3])
