-- regress_418_nested_goto_parallel_assignment: nested fallback 只在互斥路径执行一次，
-- 整条并行 value-pack 可原样进入两个 else arm。
-- unluac: expect-not-contains [[goto ]]
-- unluac: expect-not-contains [[::L]]
-- unluac: expect-not-contains [[unluac error]]
-- unluac: expect-not-contains [[unresolved]]
-- unluac: expect-order [["success"]] [["outer-fallback"]]
-- unluac: expect-order [["outer-fallback"]] [["inner-fallback"]]

local events = {}

local function pair(tag)
    events[#events + 1] = tag
    return tag, #events
end

local function choose(use_fallback, use_success, fallback_tag)
    local first, second
    if use_fallback then
        goto fallback
    end
    if use_success then
        first, second = pair("success")
        goto done
    end
    ::fallback::
    first, second = pair(fallback_tag)
    ::done::
    return first, second
end

local a, b = choose(true, true, "outer-fallback")
local c, d = choose(false, false, "inner-fallback")
local e, f = choose(false, true, "unused")

assert(a == "outer-fallback" and b == 1)
assert(c == "inner-fallback" and d == 2)
assert(e == "success" and f == 3)
assert(table.concat(events, ",") == "outer-fallback,inner-fallback,success")
