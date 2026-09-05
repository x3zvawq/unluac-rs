-- The numeric-for latch label follows cleanup on the continue path.
local log, closed = {}, {}
local function note(value)
    log[#log + 1] = value
end
local function resource(name)
    closed[name] = false
    note("open:" .. name)
    return setmetatable({}, { __close = function()
        assert(not closed[name], name .. " closed twice")
        closed[name] = true
        note("close:" .. name)
    end })
end

local function loop_exits()
    do
        local outer <close> = resource("outer")
        for i = 1, 3 do
            do
                local inner <close> = resource("inner" .. i)
                note("body:" .. i)
                if i == 1 then goto next_iteration end
                if i == 3 then break end
            end
            assert(closed["inner" .. i] and not closed.outer)
            note("after:" .. i)
            ::next_iteration::
        end
        assert(closed.inner1 and closed.inner2 and closed.inner3 and not closed.outer)
        note("after:loop")
    end
    assert(closed.outer)
    note("done")
end

loop_exits()
local actual = table.concat(log, ",")
assert(actual == "open:outer,open:inner1,body:1,close:inner1,open:inner2,body:2,close:inner2,after:2,open:inner3,body:3,close:inner3,after:loop,close:outer,done", actual)
print("loop_cleanup_label", actual)
