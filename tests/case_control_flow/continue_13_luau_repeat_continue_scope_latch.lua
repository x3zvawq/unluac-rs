-- regress_457_luau_repeat_continue_scope_latch: a repeat continue exits its nested closure scope before evaluating a nonstable condition
-- unluac: expect-not-contains [[unresolved]]
-- unluac: expect-not-contains [[unluac error]]
-- unluac: expect-ast-count [[repeat]] [[1]]
-- unluac: expect-ast-count [[continue]] [[1]]

local weak_values = setmetatable({}, { __mode = "v" })
local guard = true
local iterations = 0
local events = {}

local function selected()
    events[#events + 1] = "selected"
    collectgarbage("collect")
    guard = false
    return weak_values[1] == nil
end

local function wrong_fallback()
    events[#events + 1] = "fallback"
    return true
end

repeat
    iterations += 1
    do
        local value = {}
        weak_values[1] = value
        local capture = function()
            return value
        end
        assert(capture() == value)

        if iterations == 1 then
            continue
        end
    end
until if guard then selected() else wrong_fallback()

assert(iterations == 1, iterations)
assert(weak_values[1] == nil, "nested closure root must be released before until")
assert(table.concat(events, ",") == "selected", table.concat(events, ","))
print("regress_457_luau_repeat_continue_scope_latch", iterations, events[1])
