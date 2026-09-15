-- regress_368_repeat_closed_goto_owner: a closed goto subgraph does not bypass the repeat tail
-- unluac: expect-contains [[until mark("stop", true) or]]
-- unluac: expect-not-contains [[if mark("stop", true) then]]

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
