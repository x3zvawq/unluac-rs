-- regress_418_nested_goto_parallel_assignment: nested fallback 只在互斥路径执行一次，
-- 整条并行 value-pack 可原样进入两个 else arm。
-- unluac: expect-not-contains [[goto ]]
-- unluac: expect-not-contains [[::L]]
-- unluac: expect-not-contains [[unluac error]]
-- unluac: expect-not-contains [[unresolved]]
-- unluac: expect-order [["success"]] [["outer-fallback"]]
-- unluac: expect-order [["outer-fallback"]] [["inner-fallback"]]

-- unluac: expect-ast-count [[if]] [[1]] [[@proto=2]] [[@dialect=lua5.2]]
-- unluac: expect-ast-count [[if]] [[1]] [[@proto=2]] [[@dialect=lua5.3]]
-- unluac: expect-ast-count [[if]] [[1]] [[@proto=2]] [[@dialect=lua5.4]]
-- unluac: expect-ast-count [[if]] [[1]] [[@proto=2]] [[@dialect=lua5.5]]
-- unluac: expect-ast-count [[if]] [[1]] [[@proto=1]] [[@dialect=luajit]]
-- 两个分支直接写回同一并行结果，不为 CALL 的各个返回值累积中间别名。
-- unluac: expect-ast-count [[local-binding]] [[2]] [[@proto=2]] [[@dialect=lua5.2]]
-- unluac: expect-ast-count [[local-binding]] [[2]] [[@proto=2]] [[@dialect=lua5.3]]
-- unluac: expect-ast-count [[local-binding]] [[2]] [[@proto=2]] [[@dialect=lua5.4]]
-- unluac: expect-ast-count [[local-binding]] [[2]] [[@proto=2]] [[@dialect=lua5.5]]
-- unluac: expect-ast-count [[local-binding]] [[2]] [[@proto=1]] [[@dialect=luajit]]
-- 原 nil 初始化属于这两个声明，不拆成空声明和额外清零语句。
-- unluac: expect-ast-count [[empty-local]] [[0]] [[@proto=2]] [[@dialect=lua5.2]]
-- unluac: expect-ast-count [[empty-local]] [[0]] [[@proto=2]] [[@dialect=lua5.3]]
-- unluac: expect-ast-count [[empty-local]] [[0]] [[@proto=2]] [[@dialect=lua5.4]]
-- unluac: expect-ast-count [[empty-local]] [[0]] [[@proto=2]] [[@dialect=lua5.5]]
-- unluac: expect-ast-count [[empty-local]] [[0]] [[@proto=1]] [[@dialect=luajit]]

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
local g, h = choose(true, false, "both-false-fallback")
local i, j = choose(nil, 0, "unused")
local k, l = choose(0, nil, false)
assert(g == "both-false-fallback" and h == 4)
assert(i == "success" and j == 5)
assert(k == false and l == 6)
assert(#events == 6 and events[4] == g and events[5] == i and events[6] == false)
