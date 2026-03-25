local function reshape(head, ...vals)
    local before = vals[1] * 10 + vals[vals.n]
    vals[2] = vals[2] + head
    vals.n = vals.n + 1
    vals[vals.n] = vals[1] + vals[2] + head

    local a, b, c, d = ...
    return before, vals.n, a, b, c, d
end

print("var55-basic", reshape(4, 3, 8, 5))
