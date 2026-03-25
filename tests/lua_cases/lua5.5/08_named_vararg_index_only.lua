local function probe(idx, ...rest)
    local key = idx - 1
    return rest[idx], rest[key], rest.n, ...
end

print("var55-getvarg", probe(2, 4, 7, 5, 9))
