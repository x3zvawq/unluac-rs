-- regress_382_nested_terminal_fallback_return: an explicit empty return closes a nested
-- terminal guard, so its selected body can be lifted without capturing the parent continuation
-- unluac: expect-contains [[if not p2_1 then]]

local events = {}

local function mark(value)
    events[#events + 1] = value
end

local function nested(outer, selected)
    if outer then
        if selected then
            mark("selected")
            return 7
        end
        return
    else
        mark("parent")
        return
    end
end

assert(nested(true, true) == 7)
assert(nested(true, false) == nil)
assert(nested(false, false) == nil)
assert(table.concat(events, ",") == "selected,parent", table.concat(events, ","))
