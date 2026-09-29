-- regress_357_direct_goto_parallel_assignment: direct goto 壳应原样保留两臂的 call 与并行 value-pack
-- unluac: expect-not-contains [[goto ]]
-- unluac: expect-not-contains [[::L]]
-- unluac: expect-contains [["success"]]
-- unluac: expect-contains [["fallback"]]
-- unluac: expect-order [["success"]] [["fallback"]]

-- unluac: expect-ast-count [[if]] [[1]] [[@proto=2]] [[@dialect=lua5.2]]
-- unluac: expect-ast-count [[if]] [[1]] [[@proto=2]] [[@dialect=lua5.3]]
-- unluac: expect-ast-count [[if]] [[1]] [[@proto=2]] [[@dialect=lua5.4]]
-- unluac: expect-ast-count [[if]] [[1]] [[@proto=2]] [[@dialect=lua5.5]]
-- unluac: expect-ast-count [[if]] [[1]] [[@proto=1]] [[@dialect=luajit]]
-- unluac: expect-ast-count [[local-decl]] [[1]] [[@proto=2]] [[@dialect=lua5.2]]
-- unluac: expect-ast-count [[local-decl]] [[1]] [[@proto=2]] [[@dialect=lua5.3]]
-- unluac: expect-ast-count [[local-decl]] [[1]] [[@proto=2]] [[@dialect=lua5.4]]
-- unluac: expect-ast-count [[local-decl]] [[1]] [[@proto=2]] [[@dialect=lua5.5]]
-- unluac: expect-ast-count [[local-decl]] [[1]] [[@proto=1]] [[@dialect=luajit]]
-- unluac: expect-ast-count [[local-binding]] [[2]] [[@proto=2]] [[@dialect=lua5.2]]
-- unluac: expect-ast-count [[local-binding]] [[2]] [[@proto=2]] [[@dialect=lua5.3]]
-- unluac: expect-ast-count [[local-binding]] [[2]] [[@proto=2]] [[@dialect=lua5.4]]
-- unluac: expect-ast-count [[local-binding]] [[2]] [[@proto=2]] [[@dialect=lua5.5]]
-- unluac: expect-ast-count [[local-binding]] [[2]] [[@proto=1]] [[@dialect=luajit]]
-- unluac: expect-not-contains [[unresolved]]

local events = {}

local function pair(tag)
    events[#events + 1] = tag
    return tag, #events
end

local function choose(flag)
    local first, second
    if flag then
        first, second = pair("success")
        goto done
    end
    first, second = pair("fallback")
    ::done::
    return first, second
end

local a, b = choose(true)
local c, d = choose(false)
assert(a == "success" and b == 1)
assert(c == "fallback" and d == 2)
assert(table.concat(events, ",") == "success,fallback")
local e, f = choose(nil)
local g, h = choose(0)
local i, j = choose("")
assert(e == "fallback" and f == 3)
assert(g == "success" and h == 4)
assert(i == "success" and j == 5)
assert(table.concat(events, ",") == "success,fallback,fallback,success,success")
