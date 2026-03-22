local t = { 1, 2 }
local cached = t[1]

for i = 1, 3 do
    t[1] = i + 10
end

print("alias", cached, t[1], t[2])
