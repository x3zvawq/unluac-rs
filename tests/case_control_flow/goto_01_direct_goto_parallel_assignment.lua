-- regress_357_direct_goto_parallel_assignment: direct goto 壳应原样保留两臂的 call 与并行 value-pack
-- unluac: expect-not-contains [[goto ]]
-- unluac: expect-not-contains [[::L]]
-- unluac: expect-contains [["success"]]
-- unluac: expect-contains [["fallback"]]
-- unluac: expect-order [["success"]] [["fallback"]]

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
