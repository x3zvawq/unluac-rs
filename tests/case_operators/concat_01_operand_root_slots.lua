-- unluac: expect-ast-count [[local-binding]] [[1]] [[@proto=6]] [[@dialect=luajit]]
-- unluac: expect-ast-count [[local-binding]] [[3]] [[@proto=10]] [[@dialect=luajit]]
-- unluac: expect-ast-count [[local-binding]] [[2]] [[@proto=11]] [[@dialect=luajit]]
-- unluac: expect-ast-count [[local-binding]] [[1]] [[@proto=6]] [[@dialect=lua5.5]]
-- unluac: expect-ast-count [[local-binding]] [[1]] [[@proto=6]] [[@dialect=lua5.4]]
-- unluac: expect-ast-count [[local-binding]] [[1]] [[@proto=6]] [[@dialect=lua5.3]]
-- unluac: expect-ast-count [[local-binding]] [[1]] [[@proto=6]] [[@dialect=lua5.2]]
-- unluac: expect-ast-count [[local-binding]] [[1]] [[@proto=6]] [[@dialect=lua5.1]]
-- unluac: expect-ast-count [[local-binding]] [[3]] [[@proto=2]] [[@dialect=lua5.5]]
-- unluac: expect-ast-count [[local-binding]] [[3]] [[@proto=2]] [[@dialect=lua5.4]]
-- unluac: expect-ast-count [[local-binding]] [[3]] [[@proto=2]] [[@dialect=lua5.3]]
-- unluac: expect-ast-count [[local-binding]] [[3]] [[@proto=2]] [[@dialect=lua5.2]]
-- unluac: expect-ast-count [[local-binding]] [[2]] [[@proto=2]] [[@dialect=lua5.1]]
-- unluac: expect-ast-count [[local-binding]] [[2]] [[@proto=1]] [[@dialect=lua5.5]]
-- unluac: expect-ast-count [[local-binding]] [[2]] [[@proto=1]] [[@dialect=lua5.4]]
-- unluac: expect-ast-count [[local-binding]] [[2]] [[@proto=1]] [[@dialect=lua5.3]]
-- unluac: expect-ast-count [[local-binding]] [[2]] [[@proto=1]] [[@dialect=lua5.2]]
-- unluac: expect-ast-count [[local-binding]] [[0]] [[@proto=1]] [[@dialect=lua5.1]]
-- unluac: expect-ast-count [[function]] [[11]]
-- unluac: expect-ast-count [[if]] [[3]]
-- unluac: expect-ast-max [[local-binding]] [[20]]
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
    local concatenations = 0
    local weak = setmetatable({}, { __mode = "v" })
    local user = {}
    user.first = setmetatable({}, { __concat = function(_, tail)
        concatenations = concatenations + 1
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
        concatenations = concatenations + 1
        user.middle = nil
        user.last = nil
        return "tail"
    end })
    weak.middle = user.middle
    weak.last = user.last
    assert(render(user) == "headtail")
    assert(concatenations == 2)
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
local inspected = 0
assert(followed_by_call(user, function()
    inspected = inspected + 1
    collectgarbage("collect")
    collectgarbage("collect")
    assert(weak.last ~= nil, "concat operand root leaked into a later expression proof")
    return 5
end) == 12)
assert(inspected == 1)
-- Alias compression must retain lookup order and the right-to-left concat metamethod order.
local events = {}
local left = setmetatable({}, {__concat = function(_, tail)
    events[#events + 1] = "concat-first"
    return "Ada" .. tail, "discarded"
end})
local right = setmetatable({}, {__concat = function(prefix, _)
    events[#events + 1] = "concat-last"
    return prefix .. "Lovelace", "discarded"
end})
local indexed = setmetatable({}, {__index = function(_, key)
    events[#events + 1] = key
    if key == "first" then return left end
    if key == "middle" then return "/" end
    return right
end})
assert(rightmost(indexed) == "Ada Lovelace")
assert(table.concat(events, ",") == "first,last,concat-last,concat-first")
print("regress_466_concat_operand_root_slots", "OK")

events = {}
assert(middle(indexed) == "Ada/Lovelace")
assert(table.concat(events, ",") == "first,middle,last,concat-last,concat-first")
events = {}
assert(select("#", rightmost(indexed)) == 1)
assert(table.concat(events, ",") == "first,last,concat-last,concat-first")
assert(rightmost({ first = 0, last = 5 }) == "0 5")
assert(middle({ first = "a\0", middle = ":", last = "\0b" }) == "a\0:\0b")
assert(not pcall(rightmost, { first = false, last = "text" }))
