local function expose(idx, ...rest)
    return rest[idx], rest[idx + -1], rest.n, ...
end

print("var55-getvarg-addneg", expose(2, 4, 7, 5, 9))
