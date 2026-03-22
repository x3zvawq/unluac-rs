local function judge(a, b, c)
    local value = (a and (b or c)) or ((not b) and c)
    return value and "T" or "F"
end

print("bool", judge(true, false, true), judge(false, true, false), judge(false, false, true))
