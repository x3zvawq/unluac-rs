-- unrelated repeat conditions must not disable the minimal collective global gate
-- unluac: expect-contains [[global<const> *]]
-- unluac: expect-contains [[global<const> attr_value]]
-- unluac: expect-contains [[global attr_value]]
-- unluac: expect-contains [[global<const> setmetatable]]
-- unluac: expect-contains [[global<const> print]]
-- unluac: expect-contains [[global<const> string]]

local function run()
    local untouched_outer = nil
    global marker = 0
    global<const> assert
    repeat
        global<const> *
        print("regress436-positive")
        local untouched = nil
        local never_called = function()
            untouched = {}
        end
        local inert_copy = never_called
        inert_copy = nil
        local fresh_aggregate = {
            {},
            function()
                return true
            end,
            nested = { value = 1 },
        }
        local escaped_scalar = 1
        local inspect = function()
            if fresh_aggregate then
                print(tostring(escaped_scalar))
            end
        end
        inspect()
        marker = 1
    until (function()
        untouched_outer = {}
    end)
    assert(untouched_outer == nil)
    return marker
end

local function keeps_close_through_condition()
    local closed = false
    local function condition()
        assert(not closed)
        return true
    end

    global close_marker = 0
    global<const> assert
    repeat
        global<const> *
        local item <close> = setmetatable({}, {
            __close = function()
                closed = true
            end,
        })
        close_marker = math.max(close_marker, 1)
    until condition()
    assert(closed)
    return close_marker
end

local function keeps_invoked_closure_root()
    local weak = setmetatable({}, { __mode = "v" })
    local rooted_during_condition = false
    local function condition()
        collectgarbage("collect")
        rooted_during_condition = weak[1] ~= nil
        return true
    end

    global invoked_marker = 0
    global<const> assert
    repeat
        global<const> *
        print("regress436-invoked-closure")
        local item = nil
        local initialize = function()
            item = {}
        end
        initialize()
        weak[1] = item
        invoked_marker = 1
    until condition()
    assert(rooted_during_condition)
    return invoked_marker
end

local function keeps_invoked_self_escape_root()
    local weak = setmetatable({}, { __mode = "k" })
    local rooted_during_condition = false
    local function condition()
        collectgarbage("collect")
        rooted_during_condition = next(weak) ~= nil
        return true
    end

    global self_escape_marker = 0
    global<const> assert
    repeat
        global<const> *
        print("regress436-self-escape")
        local self
        self = function()
            weak[self] = true
        end
        self()
        self_escape_marker = 1
    until condition()
    assert(rooted_during_condition)
    return self_escape_marker
end

local function keeps_complex_lvalue_key_root()
    local weak = setmetatable({}, { __mode = "k" })
    local rooted_during_condition = false
    local function condition()
        collectgarbage("collect")
        rooted_during_condition = next(weak) ~= nil
        return true
    end

    global complex_key_marker = 0
    global<const> assert
    repeat
        global<const> *
        local key = {}
        weak[key] = key
        complex_key_marker = 1
    until condition()
    assert(rooted_during_condition)
    return complex_key_marker
end

local function keeps_returned_capture_root()
    local weak = setmetatable({}, { __mode = "v" })
    local rooted_during_condition = false
    local function condition()
        collectgarbage("collect")
        rooted_during_condition = weak[1] ~= nil
        return true
    end

    global returned_capture_marker = 0
    global<const> assert
    repeat
        global<const> *
        print("regress436-returned-capture")
        local item = {}
        weak[1] = (function()
            return item
        end)()
        returned_capture_marker = 1
    until condition()
    assert(rooted_during_condition)
    return returned_capture_marker
end

local function keeps_nested_called_closure_escape_root()
    local weak = setmetatable({}, { __mode = "v" })
    local rooted_during_condition = false
    local function condition()
        collectgarbage("collect")
        rooted_during_condition = weak[1] ~= nil
        return true
    end

    global nested_escape_marker = 0
    global<const> assert
    repeat
        global<const> *
        print("regress436-nested-closure-escape")
        local item = {}
        local function outer()
            local function inner()
                weak[1] = item
            end
            inner()
            inner()
        end
        outer()
        outer()
        nested_escape_marker = 1
    until condition()
    assert(rooted_during_condition)
    return nested_escape_marker
end

local function keeps_sibling_called_closure_escape_root()
    local weak = setmetatable({}, { __mode = "v" })
    local rooted_during_condition = false
    local function condition()
        collectgarbage("collect")
        rooted_during_condition = weak[1] ~= nil
        return true
    end

    global sibling_escape_marker = 0
    global<const> assert
    repeat
        global<const> *
        print("regress436-sibling-closure-escape")
        local item = {}
        local function inner()
            weak[1] = item
        end
        local function outer()
            inner()
        end
        outer()
        outer()
        sibling_escape_marker = 1
    until condition()
    assert(rooted_during_condition)
    return sibling_escape_marker
end

local function keeps_outer_handoff_root()
    local weak = setmetatable({}, { __mode = "v" })
    local value = { x = 1, y = 2 }
    weak[1] = value
    local rooted_during_condition = false
    local function condition()
        collectgarbage("collect")
        rooted_during_condition = weak[1] ~= nil
        return true
    end

    global handoff_marker = 0
    global<const> assert
    repeat
        global<const> *
        string.len("x")
        local copy = value
        handoff_marker = copy.x
        handoff_marker = handoff_marker + copy.y
        value = nil
    until condition()
    assert(rooted_during_condition)
    return handoff_marker
end

local function reopens_named_const_for_write(flag)
    global attr_gate = 0
    global<const> assert
    global<const> attr_value
    local before = attr_value
    if flag then
        global attr_value
        attr_value = 2
    end
    assert(before == nil)
    return attr_value
end

assert(run() == 1)
assert(keeps_close_through_condition() == 1)
assert(keeps_invoked_closure_root() == 1)
assert(keeps_invoked_self_escape_root() == 1)
assert(keeps_complex_lvalue_key_root() == 1)
assert(keeps_returned_capture_root() == 1)
assert(keeps_nested_called_closure_escape_root() == 1)
assert(keeps_sibling_called_closure_escape_root() == 1)
assert(keeps_outer_handoff_root() == 3)
assert(reopens_named_const_for_write(true) == 2)
print("regress_436_lua55_repeat_collective_scope")
