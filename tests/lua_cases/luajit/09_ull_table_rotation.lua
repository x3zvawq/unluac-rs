local queue = { 7ULL, 11ULL, 19ULL, 23ULL, 31ULL }
local acc = 5ULL

for step = 1, 7 do
    local head = table.remove(queue, 1)

    if step % 3 == 0 then
        acc = acc + head * 2ULL
        queue[#queue + 1] = head + step
    else
        acc = acc * 2ULL - head + step
        queue[#queue + 1] = head + 1ULL
    end
end

local parts = {}

for i = 1, #queue do
    parts[i] = tostring(queue[i])
end

print("luajit-rotation", tostring(acc), table.concat(parts, "|"))
