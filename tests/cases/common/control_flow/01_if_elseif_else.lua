local function classify(x)
    if x > 0 then
        return "pos"
    end

    if x == 0 then
        return "zero"
    end

    return "neg"
end

print("if", classify(3), classify(0), classify(-2))
