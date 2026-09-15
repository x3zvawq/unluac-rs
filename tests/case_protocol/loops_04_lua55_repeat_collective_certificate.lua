-- Safe repeat suffixes keep a collective gate, while escaped roots remain live through until.
-- unluac: expect-contains [[global<const> *]]
-- unluac: expect-contains [[global<const> print]]
-- unluac: expect-order [[global<const> *]] [[string.len("safe")]]
-- unluac: expect-order [[string.len("safe")]] [[global<const> print]]
-- unluac: expect-order [[global<const> print]] [[print("unsafe")]]
-- unluac: expect-ast-count [[repeat]] [[2]]

local function safe(flag)
    global safe_marker = 0
    global<const> assert
    repeat
        global<const> *
        string.len("safe")
        local value = { x = 1, y = 2 }
        safe_marker = value.x + value.y
        safe_marker = safe_marker + value.x
    until flag
    return safe_marker
end

local function unsafe()
    local weak = setmetatable({}, { __mode = "v" })
    local rooted = false
    local function observe()
        collectgarbage("collect")
        rooted = weak[1] ~= nil
        return true
    end

    global unsafe_marker = 0
    global<const> assert
    repeat
        global<const> *
        print("unsafe")
        local item = {}
        (function()
            weak[1] = item
        end)()
        unsafe_marker = 1
    until observe()
    assert(rooted, "escaped repeat root collected before condition")
    return unsafe_marker
end

assert(safe(true) == 4)
assert(unsafe() == 1)
