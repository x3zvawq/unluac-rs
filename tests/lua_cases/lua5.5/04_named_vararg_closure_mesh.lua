local function weave(scale, ...pack)
    local function bump(index, extra)
        pack[index] = pack[index] * scale + extra
        return pack[index]
    end

    local first = bump(1, scale)
    local tail = bump(pack.n, first - scale)
    pack.n = pack.n + 1
    pack[pack.n] = first - tail

    local function nudge()
        pack[2] = pack[2] + pack.n
        return pack[2]
    end

    local second = nudge()
    local a, b, c, d = ...
    return first, second, tail, pack.n, a, b, c, d
end

print("var55-closure", weave(2, 4, 7, 5))
