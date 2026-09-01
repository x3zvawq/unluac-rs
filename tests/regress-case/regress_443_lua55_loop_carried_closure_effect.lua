-- Loop-carried closure effects must reach a fixed point before AST readability consumes roots.

local weak
local rooted_during_condition

local function reset_probe()
    weak = setmetatable({}, { __mode = "v" })
    rooted_during_condition = false
end

local function sink(value)
    weak[1] = value
end

local function condition()
    collectgarbage("collect")
    rooted_during_condition = weak[1] ~= nil
    return true
end

local function iterator(_, control)
    control = control + 1
    if control <= 3 then
        return control
    end
end

local function probe_while()
    reset_probe()
    global loop_while_marker = 0
    repeat
        global<const> *
        print("regress443-while")
        local item = {}
        local function work()
            local a, b
            local i = 0
            while i < 3 do
                sink(a)
                a = b
                b = item
                i = i + 1
            end
        end
        work()
        work()
        loop_while_marker = 1
    until condition()
    return rooted_during_condition
end

local function probe_repeat()
    reset_probe()
    global loop_repeat_marker = 0
    repeat
        global<const> *
        print("regress443-repeat")
        local item = {}
        local function work()
            local a, b
            local i = 0
            repeat
                sink(a)
                a = b
                b = item
                i = i + 1
            until i == 3
        end
        work()
        work()
        loop_repeat_marker = 1
    until condition()
    return rooted_during_condition
end

local function probe_numeric_for()
    reset_probe()
    global loop_numeric_marker = 0
    repeat
        global<const> *
        print("regress443-numeric")
        local item = {}
        local function work()
            local a, b
            for _ = 1, 3 do
                sink(a)
                a = b
                b = item
            end
        end
        work()
        work()
        loop_numeric_marker = 1
    until condition()
    return rooted_during_condition
end

local function probe_generic_for()
    reset_probe()
    global loop_generic_marker = 0
    repeat
        global<const> *
        print("regress443-generic")
        local item = {}
        local function work()
            local a, b
            for _ in iterator, nil, 0 do
                sink(a)
                a = b
                b = item
            end
        end
        work()
        work()
        loop_generic_marker = 1
    until condition()
    return rooted_during_condition
end

local function probe_loop_carried_callee()
    reset_probe()
    global loop_callee_marker = 0
    repeat
        global<const> *
        print("regress443-callee")
        local item = {}
        local function noop()
            return nil
        end
        local function escape()
            weak[1] = item
        end
        local function work()
            local invoke = noop
            for _ = 1, 2 do
                invoke()
                invoke = escape
            end
        end
        work()
        work()
        loop_callee_marker = 1
    until condition()
    return rooted_during_condition
end

local while_ok = probe_while()
local repeat_ok = probe_repeat()
local numeric_ok = probe_numeric_for()
local generic_ok = probe_generic_for()
local callee_ok = probe_loop_carried_callee()
assert(while_ok, "while loop-carried captured root lost")
assert(repeat_ok, "repeat loop-carried captured root lost")
assert(numeric_ok, "numeric-for loop-carried captured root lost")
assert(generic_ok, "generic-for loop-carried captured root lost")
assert(callee_ok, "loop-carried callee root lost")
print("regress_443_lua55_loop_carried_closure_effect", "OK")
