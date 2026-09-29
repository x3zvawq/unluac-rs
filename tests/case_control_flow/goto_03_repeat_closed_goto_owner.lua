-- regress_368_repeat_closed_goto_owner: a closed goto subgraph does not bypass the repeat tail
-- unluac: expect-contains [[until mark("stop", true) or]]
-- unluac: expect-not-contains [[if mark("stop", true) then]]

-- unluac: expect-ast-count [[repeat]] [[1]] [[@proto=2]] [[@dialect=lua5.2]]
-- unluac: expect-ast-count [[repeat]] [[1]] [[@proto=2]] [[@dialect=lua5.3]]
-- unluac: expect-ast-count [[repeat]] [[1]] [[@proto=2]] [[@dialect=lua5.4]]
-- unluac: expect-ast-count [[repeat]] [[1]] [[@proto=2]] [[@dialect=lua5.5]]
-- unluac: expect-ast-count [[repeat]] [[1]] [[@proto=1]] [[@dialect=luajit]]
-- unluac: expect-ast-count [[while]] [[0]] [[@proto=2]] [[@dialect=lua5.2]]
-- unluac: expect-ast-count [[while]] [[0]] [[@proto=2]] [[@dialect=lua5.3]]
-- unluac: expect-ast-count [[while]] [[0]] [[@proto=2]] [[@dialect=lua5.4]]
-- unluac: expect-ast-count [[while]] [[0]] [[@proto=2]] [[@dialect=lua5.5]]
-- unluac: expect-ast-count [[while]] [[0]] [[@proto=1]] [[@dialect=luajit]]
-- unluac: expect-ast-count [[goto]] [[2]] [[@proto=2]] [[@dialect=lua5.2]]
-- unluac: expect-ast-count [[goto]] [[2]] [[@proto=2]] [[@dialect=lua5.3]]
-- unluac: expect-ast-count [[goto]] [[2]] [[@proto=2]] [[@dialect=lua5.4]]
-- unluac: expect-ast-count [[goto]] [[2]] [[@proto=2]] [[@dialect=lua5.5]]
-- unluac: expect-ast-count [[goto]] [[2]] [[@proto=1]] [[@dialect=luajit]]
-- unluac: expect-ast-count [[label]] [[2]] [[@proto=2]] [[@dialect=lua5.2]]
-- unluac: expect-ast-count [[label]] [[2]] [[@proto=2]] [[@dialect=lua5.3]]
-- unluac: expect-ast-count [[label]] [[2]] [[@proto=2]] [[@dialect=lua5.4]]
-- unluac: expect-ast-count [[label]] [[2]] [[@proto=2]] [[@dialect=lua5.5]]
-- unluac: expect-ast-count [[label]] [[2]] [[@proto=1]] [[@dialect=luajit]]
-- unluac: expect-ast-count [[break]] [[0]] [[@proto=2]] [[@dialect=lua5.2]]
-- unluac: expect-ast-count [[break]] [[0]] [[@proto=2]] [[@dialect=lua5.3]]
-- unluac: expect-ast-count [[break]] [[0]] [[@proto=2]] [[@dialect=lua5.4]]
-- unluac: expect-ast-count [[break]] [[0]] [[@proto=2]] [[@dialect=lua5.5]]
-- unluac: expect-ast-count [[break]] [[0]] [[@proto=1]] [[@dialect=luajit]]
-- unluac: expect-not-contains [[unresolved]]

local events = {}

function mark(name, value)
    events[#events + 1] = name
    return value
end

local function run(entry, cycle, again)
    repeat
        if entry then
            goto second
        end
        ::first::
        mark("first", false)
        ::second::
        mark("second", false)
        if cycle then
            goto first
        end
        if mark("stop", true) then
            break
        end
    until again
    return table.concat(events, ",")
end

assert(run(true, false, false) == "second,stop")
-- cycle=true 的闭合子图不终止；覆盖其余入口及 repeat 尾值组合。
for mask = 0, 3 do
    events = {}
    local entry = mask % 2 == 1
    local again = mask >= 2
    local want = entry and "second,stop" or "first,second,stop"
    assert(run(entry, false, again) == want)
end
events = {}
assert(run(nil, nil, 0) == "first,second,stop")
