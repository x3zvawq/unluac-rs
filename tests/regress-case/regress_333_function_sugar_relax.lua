-- unluac: expect-contains [[:capture_root(p]]
-- unluac: expect-contains [[:effectful_relaxed(]]

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
