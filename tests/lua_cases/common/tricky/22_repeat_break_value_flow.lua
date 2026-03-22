local i = 0
local sum = 0

repeat
    i = i + 1

    if i % 2 == 0 then
        sum = sum + i * 3
    else
        sum = sum + i
    end

    if sum > 10 then
        break
    end
until i >= 6

print("repeat-break", i, sum)
