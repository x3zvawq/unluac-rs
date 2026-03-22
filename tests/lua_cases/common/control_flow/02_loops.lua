local total = 0
local i = 1

while i <= 3 do
    total = total + i
    i = i + 1
end

for j = 4, 6 do
    total = total + j
end

print("loop", total)
