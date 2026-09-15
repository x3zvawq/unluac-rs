-- regress_466_concat_operand_root_slots: distinguish the rightmost slot from overwritten middle slots.
local function rightmost(user)
    local first = user.first
    local last = user.last
    return first .. " " .. last
end

local function middle(user)
    local first = user.first
    local center = user.middle
    local last = user.last
    return first .. center .. last
end

local function check(render, needs_middle)
    local weak = setmetatable({}, { __mode = "v" })
    local user = {}
    user.first = setmetatable({}, { __concat = function(_, tail)
        collectgarbage("collect")
        collectgarbage("collect")
        assert(weak.last ~= nil, "rightmost lookup snapshot lost during concat")
        if needs_middle then
            assert(weak.middle ~= nil, "middle lookup snapshot lost during concat")
        end
        return "head" .. tail
    end })
    user.middle = {}
    user.last = setmetatable({}, { __concat = function(_, _)
        user.middle = nil
        user.last = nil
        return "tail"
    end })
    weak.middle = user.middle
    weak.last = user.last
    assert(render(user) == "headtail")
end
check(rightmost, false)
check(middle, true)

-- A new expression after CONCAT may reuse even the rightmost temporary slot.
local function followed_by_call(user, inspect)
    local last = user.last
    return ("" .. last) + inspect()
end
local weak = setmetatable({}, { __mode = "v" })
local user = {}
user.last = setmetatable({}, { __concat = function(_, _)
    user.last = nil
    return "7"
end })
weak.last = user.last
assert(followed_by_call(user, function()
    collectgarbage("collect")
    collectgarbage("collect")
    assert(weak.last ~= nil, "concat operand root leaked into a later expression proof")
    return 5
end) == 12)
-- Alias compression must retain lookup order and the right-to-left concat metamethod order.
local events = {}
local left = setmetatable({}, {__concat = function(_, tail)
    events[#events + 1] = "concat-first"
    return "Ada" .. tail
end})
local right = setmetatable({}, {__concat = function(prefix, _)
    events[#events + 1] = "concat-last"
    return prefix .. "Lovelace"
end})
local indexed = setmetatable({}, {__index = function(_, key)
    events[#events + 1] = key
    if key == "first" then return left end
    return right
end})
assert(rightmost(indexed) == "Ada Lovelace")
assert(table.concat(events, ",") == "first,last,concat-last,concat-first")
print("regress_466_concat_operand_root_slots", "OK")
