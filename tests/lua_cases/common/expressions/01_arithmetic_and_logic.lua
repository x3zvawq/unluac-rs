local x = 5 + 3 * 2
local label = (x > 10) and "gt" or "le"
local inverted = not (x == 11)

print("expr", x, label, inverted)
