global none, print
global score = 6

local function inspect(tag)
    local shadow = #tag + 1

    do
        global<const> *
        local left = math.max(shadow, score)
        local right = tostring(shadow) .. ":" .. tostring(score)
        return left, right
    end
end

local a, b = inspect("abc")
score = score + a

print("g55-const", a, b, score)
