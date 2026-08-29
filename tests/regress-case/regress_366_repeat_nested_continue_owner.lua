-- regress_366_repeat_nested_continue_owner: an inner-loop continue does not skip the outer repeat tail condition
-- unluac: expect-contains [[until mark("stop", true) or mark("again", false)]]

local events = {}

function mark(name, value)
    events[#events + 1] = name
    return value
end

repeat
    for index = 1, 2 do
        if index == 1 then
            continue
        end
        events[#events + 1] = "inner"
    end
    if mark("stop", true) then
        break
    end
until mark("again", false)

assert(table.concat(events, ",") == "inner,stop")
