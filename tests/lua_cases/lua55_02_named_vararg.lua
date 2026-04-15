-- lua55_02_named_vararg#1: 命名变参基础
local function test_basic()
    local function reshape(head, ...vals)
        local before = vals[1] * 10 + vals[vals.n]
        vals[2] = vals[2] + head
        vals.n = vals.n + 1
        vals[vals.n] = vals[1] + vals[2] + head

        local a, b, c, d = ...
        return before, vals.n, a, b, c, d
    end

    print("lua55_02_named_vararg#1", reshape(4, 3, 8, 5))
end

-- lua55_02_named_vararg#2: 命名变参闭包交叉
local function test_closure_mesh()
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

    print("lua55_02_named_vararg#2", weave(2, 4, 7, 5))
end

-- lua55_02_named_vararg#3: 命名变参管线
local function test_pipeline()
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

    print("lua55_02_named_vararg#3", warmup_a, warmup_b, warmup_c, i1, i2, i3, i4)
    print("lua55_02_named_vararg#3", p2, n2, s2)
end

-- lua55_02_named_vararg#4: 命名变参返回
local function test_return()
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

    print("lua55_02_named_vararg#4", pack[1], pack[2], pack[3], pack.n, meta.first, meta.last, meta.n)
end

-- lua55_02_named_vararg#5: 命名变参仅索引
local function test_index_only()
    local function probe(idx, ...rest)
        local key = idx - 1
        return rest[idx], rest[key], rest.n, ...
    end

    print("lua55_02_named_vararg#5", probe(2, 4, 7, 5, 9))
end

-- lua55_02_named_vararg#6: 命名变参索引正负
local function test_index_addneg()
    local function expose(idx, ...rest)
        return rest[idx], rest[idx + -1], rest.n, ...
    end

    print("lua55_02_named_vararg#6", expose(2, 4, 7, 5, 9))
end

test_basic()
test_closure_mesh()
test_pipeline()
test_return()
test_index_only()
test_index_addneg()
