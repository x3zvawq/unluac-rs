local start, stop, step = 1, 7, 2
local values = {}

for i = start, stop, step do
    values[#values + 1] = i
    start = 100
    step = 100
end

print("for-bound", table.concat(values, ","), start, step)
