-- regress_234_nested_phi_short_value_merge#1: 短路值叶经中间 Phi 汇入外层 merge
-- unluac: expect-not-contains [[unluac error]]
-- unluac: expect-not-contains [[unresolved]]
-- unluac: expect-not-contains [[if p2_1 then]]
-- unluac: expect-not-contains [[local r1_0 = p1_1 or p1_0]]
local function pick(x, a, b, c)
    local out
    if x then
        out = a or x
    else
        out = (b and (c and "maybe" or "no")) or x
    end
    return out
end

local first = pick(true, true, false, true)
local second = pick(false, false, true, true)
local third = pick(false, false, true, false)
local fourth = pick(false, false, false, true)
assert(first == true)
assert(second == "maybe")
assert(third == "no")
assert(fourth == false)
print(first, second, third, fourth)

local function shared_fallback(x, a, b, c)
    local out
    if x then
        out = a and ((x == true and "yes") or (c and "maybe") or "no")
            or x
            or (b and ((x == true and "yes") or (c and "maybe") or "no"))
            or x
    else
        out = x
            or (b and ((x == true and "yes") or (c and "maybe") or "no"))
            or x
    end
    return out or "false"
end

assert(shared_fallback(true, true, false, true) == "yes")
assert(shared_fallback(false, false, true, true) == "maybe")
assert(shared_fallback(false, false, false, true) == "false")

local repeated_calls = 0
local function same_call()
    repeated_calls = repeated_calls + 1
    return repeated_calls == 1
end

local function call_twice_on_truthy_path()
    local value
    if same_call() then
        value = same_call()
    else
        value = "not called"
    end
    return value
end

assert(call_twice_on_truthy_path() == false)
assert(repeated_calls == 2)
