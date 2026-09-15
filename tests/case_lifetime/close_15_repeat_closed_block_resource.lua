-- regress_371_repeat_closed_block_resource: a completed lexical block closes before the repeat tail
-- unluac: expect-contains [[until mark("stop", true) or mark("again", false)]]

local events = {}

local close_meta = {
    __close = function()
        events[#events + 1] = "close"
    end,
}

function mark(name, value)
    events[#events + 1] = name
    return value
end

repeat
    do
        local resource <close> = setmetatable({}, close_meta)
        events[#events + 1] = "body"
    end
    if mark("stop", true) then
        break
    end
until mark("again", false)

assert(table.concat(events, ",") == "body,close,stop")

-- The false guard must reach the repeat condition after the resource closes.
events = {}
repeat
    do
        local resource <close> = setmetatable({}, close_meta)
        events[#events + 1] = "body"
    end
    if mark("stop", false) then
        break
    end
until mark("again", true)
assert(table.concat(events, ",") == "body,close,stop,again")
