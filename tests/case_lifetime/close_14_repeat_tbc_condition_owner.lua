-- regress_369_repeat_tbc_condition_owner: repeat-owner TBC must close after the tail break guard
-- unluac: expect-contains [[if mark("stop", true) then]]
-- unluac: expect-not-contains [[until mark("stop", true) or]]

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
