local function expose(flag, ...rest)
    if flag then
        return rest
    end

    return {
        first = rest[1],
        last = rest[rest.n],
        n = rest.n,
    }
end

local pack = expose(true, 3, 8, 5)
local meta = expose(false, 7, 9)

print("var55-return", pack[1], pack[2], pack[3], pack.n, meta.first, meta.last, meta.n)
