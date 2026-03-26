local samples = { 1i, 2i, -3i, 4i, -5i }
local score = 0LL
local tags = {}

for index = 1, #samples do
    local rendered = tostring(samples[index])
    local sign = rendered:find("%-") and "neg" or "pos"
    local magnitude = tonumber((rendered:match("(%d+)i$")))

    if sign == "neg" then
        score = score - magnitude * 2LL + index
    else
        score = score + magnitude * 3LL - index
    end

    tags[#tags + 1] = rendered .. ":" .. sign
end

print("luajit-imag", table.concat(tags, "|"), tostring(score))
