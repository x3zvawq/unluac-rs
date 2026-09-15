-- regress_367_repeat_nested_close_owner: a nested loop closes its resources before the outer repeat tail
-- unluac: expect-contains [[until mark("stop", true) or mark("again", false)]]

local events = {}

local close_meta = {
    __close = function(value)
        events[#events + 1] = "close:" .. value.label
    end,
}

function mark(name, value)
    events[#events + 1] = name
    return value
end

repeat
    for index = 1, 1 do
        local resource <close> = setmetatable({ label = index }, close_meta)
        events[#events + 1] = "body:" .. resource.label
    end
    if mark("stop", true) then
        break
    end
until mark("again", false)

assert(table.concat(events, ",") == "body:1,close:1,stop")
