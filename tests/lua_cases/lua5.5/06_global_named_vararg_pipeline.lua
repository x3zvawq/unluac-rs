global none, print, table
global registry = {}
global warmup_a, warmup_b, warmup_c = "", 0, ""

global function install(kind, base, ...vals)
    local prefix = kind .. ":" .. base
    local factor = #kind + base

    local function spin(extra)
        vals[1] = vals[1] + extra
        local last = vals[vals.n] * factor - extra
        vals[vals.n] = last
        vals.n = vals.n + 1
        vals[vals.n] = vals[1] + last + base
        return prefix, vals.n, table.concat(vals, "|")
    end

    warmup_a, warmup_b, warmup_c = spin(2)
    registry[kind] = spin

    local a, b, c, d = ...
    return a, b, c, d
end

local i1, i2, i3, i4 = install("ax", 3, 4, 6, 8)
local p2, n2, s2 = registry.ax(1)

print("mix55", warmup_a, warmup_b, warmup_c, i1, i2, i3, i4)
print("mix55", p2, n2, s2)
