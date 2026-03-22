local i = 0
local values = {}

repeat
    i = i + 1
    values[i] = i * i
until i >= 4

print("repeat", table.concat(values, ","))
