-- regress_382_nested_terminal_fallback_return: an explicit empty return closes a nested
-- terminal guard, so its selected body can be lifted without capturing the parent continuation
-- unluac: expect-contains [[if not p2_1 then]]
-- 两臂都是 return 时仍由空 return guard 负责规范化，不能与正向条件整理互相翻转。
-- unluac: expect-contains [[if not p3_1 then]]
-- unluac: expect-ast-count [[local-binding]] [[4]]
-- unluac: expect-ast-count [[if]] [[4]]

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

local function direct(outer, selected)
    if outer then
        if selected then
            return 7
        end
        return
    else
        return 9
    end
end

assert(nested(true, true) == 7)
assert(nested(true, false) == nil)
assert(nested(false, false) == nil)
assert(table.concat(events, ",") == "selected,parent", table.concat(events, ","))
assert(direct(true, true) == 7)
assert(direct(true, false) == nil)
assert(direct(false, true) == 9)
assert(direct(0, "") == 7)
assert(direct(nil, true) == 9)
assert(direct(true, nil) == nil)
assert(nested(0, "") == 7)
assert(nested("", nil) == nil)
assert(nested(nil, true) == nil)
assert(table.concat(events, ",") == "selected,parent,selected,parent")
