-- regress_369_repeat_tbc_condition_owner: repeat-owner TBC must close after the tail break guard
-- unluac: expect-contains [[if mark("stop", true) then]]
-- unluac: expect-not-contains [[until mark("stop", true) or]]
-- unluac: expect-ast-count [[local-binding]] [[5]]
-- unluac: expect-ast-count [[close-binding]] [[3]]
-- unluac: expect-ast-count [[repeat]] [[3]]
-- unluac: expect-ast-count [[break]] [[3]]

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
    local resource <close> = setmetatable({}, close_meta)
    if mark("stop", true) then
        break
    end
until mark("again", false)

assert(table.concat(events, ",") == "stop,close")

events = {}
repeat
    local resource <close> = setmetatable({}, close_meta)
    if mark("stop", false) then
        break
    end
until mark("again", true)
assert(table.concat(events, ",") == "stop,again,close")

events = {}
repeat
    local resource <close> = setmetatable({}, close_meta)
    if mark("stop", false) then
        break
    end
until mark("again", #events >= 4)
assert(table.concat(events, ",") == "stop,again,close,stop,again,close")
