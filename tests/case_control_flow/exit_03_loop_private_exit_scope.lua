-- unluac: expect-ast-min [[while]] [[2]]
-- unluac: expect-ast-min [[break]] [[1]]
local events = {}
local function resource(label)
    return setmetatable({}, {
        __close = function()
            events[#events + 1] = "close:" .. label
        end,
    })
end

local function with_close()
    local index = 0
    while true do
        local guard <close> = resource("iteration")
        index = index + 1
        if index == 2 then
            events[#events + 1] = "private"
            break
        end
        events[#events + 1] = "body"
    end
    events[#events + 1] = "public"
end

local function external_entry(skip)
    local index = 0
    if skip then goto shared end
    while true do
        index = index + 1
        if index == 2 then goto shared end
        events[#events + 1] = "loop"
    end
    ::shared::
    events[#events + 1] = "shared:" .. index
end

with_close()
external_entry(true)
external_entry(false)
assert(table.concat(events, ",") ==
    "body,close:iteration,private,close:iteration,public,shared:0,loop,shared:2")
print("loop-private-scope", table.concat(events, ","))
