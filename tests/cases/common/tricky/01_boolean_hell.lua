local function boolean_hell(a, b, c, d)
    local x = (a and (b or c) and not d) or ((a or d) and (b and c))

    if (x and a) or (not x and b) then
        x = (x == true) and "yes" or (c and "maybe" or "no")
    end

    return x and x or "false"
end

print("boolhell", boolean_hell(true, false, true, false))
print("boolhell", boolean_hell(false, true, true, false))
print("boolhell", boolean_hell(false, false, true, true))
