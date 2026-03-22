local function control_flow(x)
    local out = 0

    if x > 10 then
        local a = x * 2
        if a % 3 == 0 then
            out = a
        else
            out = a + 1
        end
    elseif x > 5 then
        repeat
            out = out + 1
            if out == 7 then
                break
            end
        until out > 10
    else
        for i = 1, 5 do
            out = out + i
        end
    end

    local val = x > 0 and "positive" or "negative"
    return out, val
end

for _, x in ipairs({ 12, 8, 3, -1 }) do
    local out, val = control_flow(x)
    print("flow", x, out, val)
end
