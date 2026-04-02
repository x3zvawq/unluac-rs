local source = {
    [1] = "a",
    [3] = "c",
}

local out = {}

for i = 1, 3 do
    local value = source[i]

    if value then
        out[#out + 1] = value .. i
    end
end

print("loop-tail-guard", table.concat(out, "|"))
