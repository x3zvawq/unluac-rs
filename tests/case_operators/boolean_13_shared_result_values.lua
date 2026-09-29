-- Normal result facts must preserve nil/false, selected object identity and operator events.
-- unluac: expect-not-contains [[unluac error]]
-- unluac: expect-not-contains [[unresolved]]
-- unluac: expect-ast-count [[function]] [[5]]
-- unluac: expect-ast-count [[if]] [[0]]
-- unluac: expect-ast-max [[local-binding]] [[22]]
local function choose(value)
    local falsy = value and false
    local truthy = value or true
    return falsy, falsy or false, truthy, truthy and true, not truthy
end

local a, b, c, d, e = choose(nil)
assert(a == nil and b == false and c == true and d == true and e == false)
a, b, c, d, e = choose(false)
assert(a == false and b == false and c == true and d == true and e == false)
local object = {}
a, b, c, d, e = choose(object)
assert(a == false and b == false and rawequal(c, object) and d == true and e == false)
a, b, c, d, e = choose(0)
assert(a == false and b == false and c == 0 and d == true and e == false)

local function numeric(flag)
    local left = flag and 1 or 2
    local right = flag and 3 or 4
    return not -(left + right), not #"abc"
end
local n1, n2 = numeric(true)
assert(n1 == false and n2 == false)
n1, n2 = numeric(false)
assert(n1 == false and n2 == false)

local additions, negations = 0, 0
local operator_result = false
local operator_trace = ""
local special = setmetatable({}, {
    __add = function(left, right)
        assert(rawequal(left, right))
        additions = additions + 1
        operator_trace = operator_trace .. "add,"
        return operator_result
    end,
    __unm = function()
        negations = negations + 1
        operator_trace = operator_trace .. "neg,"
        return operator_result
    end,
})
local function operators(value)
    return not (value + value), not -value
end
local o1, o2 = operators(special)
assert(o1 == true and o2 == true and additions == 1 and negations == 1)
print("regress_511_shared_result_values", "OK")
assert(operator_trace == "add,neg,")
operator_result = nil
o1, o2 = operators(special)
assert(o1 == true and o2 == true and additions == 2 and negations == 2)
operator_result = object
o1, o2 = operators(special)
assert(o1 == false and o2 == false and additions == 3 and negations == 3)
assert(operator_trace == "add,neg,add,neg,add,neg,")
assert(select("#", operators(special)) == 2)
assert(additions == 4 and negations == 4)
o1, o2 = operators(0)
assert(o1 == false and o2 == false and additions == 4 and negations == 4)
a, b, c, d, e = choose("")
assert(a == false and b == false and c == "" and d == true and e == false)
assert(select("#", choose(nil)) == 5 and select("#", numeric(nil)) == 2)
