-- regress_343_generic_for_vararg_pack: exact vararg producer 恢复为 loop head 的 open tail。
-- unluac: expect-contains [[in next, ... do]]

local function collect(...)
    local out = {}
    for key, value in next, ... do
        out[#out + 1] = key .. ":" .. value
    end
    table.sort(out)
    return table.concat(out, ",")
end

assert(collect({ a = 1, b = 2 }) == "a:1,b:2")
print("regress_343_generic_for_vararg_pack")
