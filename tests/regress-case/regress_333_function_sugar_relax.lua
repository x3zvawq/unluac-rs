-- Assignment-to-method syntax is retained as plain field syntax without explicit provenance.
-- unluac: expect-contains [[.capture_root(p]]
-- unluac: expect-contains [[:effectful_relaxed(]]
-- unluac: expect-contains [[:direct_statement_only()]]
-- unluac: expect-contains [[()()]]

local root_object = {}
root_object.capture_root = function(receiver, value)
    return receiver == root_object and value
end

assert(root_object:capture_root(37) == 37)

local effect_count = 0
local method_owner = {}
function method_owner:effectful_relaxed(value)
    return value
end

local function make_method_owner()
    effect_count = effect_count + 1
    return method_owner
end

local effect_receiver = make_method_owner()
local effect_result = effect_receiver.effectful_relaxed(effect_receiver, 43)
assert(effect_result == 43 and effect_count == 1)

-- A direct call statement has the same two-use receiver snapshot as an assigned call.
local direct_call_count = 0
local function make_direct_call_receiver()
    direct_call_count = direct_call_count + 1
    return {
        direct_statement_only = function(self)
            direct_call_count = direct_call_count + 1
        end,
    }
end
local direct_receiver = make_direct_call_receiver()
direct_receiver.direct_statement_only(direct_receiver)
assert(direct_call_count == 2)

-- A write target is not a read use; removing its alias declaration would retarget the write.
local write_target_receiver = {
    touch = function(self)
        return "inner"
    end,
}
local receiver = "outer"
local observed_receiver = "unset"
local function write_target_probe(flag)
    local receiver = flag and write_target_receiver
    receiver = receiver.touch(receiver)
    observed_receiver = receiver
    return receiver
end
assert(write_target_probe(true) == "inner")
assert(receiver == "outer")
assert(observed_receiver == "inner")
assert(write_target_receiver.touch(write_target_receiver) == "inner")

local constructor_events = {}
local function mark(name)
    constructor_events[#constructor_events + 1] = name
    return name
end

local function consume(outer, middle)
    return outer.child.tag, middle
end

local function build_constructor()
    local callee = consume
    local outer = { tag = mark("outer") }
    local middle = mark("middle")
    local inner = { tag = mark("inner") }
    outer.child = inner
    return callee(outer, middle)
end

local inner_tag, middle_tag = build_constructor()
assert(inner_tag == "inner" and middle_tag == "middle")
assert(table.concat(constructor_events, ",") == "outer,middle,inner")

print("function-sugar-relax", inner_tag, middle_tag)

local terminal_callee_events = 0
local function make_terminal_callee()
    terminal_callee_events = terminal_callee_events + 1
    return function()
        terminal_callee_events = terminal_callee_events + 1
    end
end

local terminal_callee = make_terminal_callee()
terminal_callee()
assert(terminal_callee_events == 2)
