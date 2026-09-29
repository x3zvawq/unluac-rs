-- regress_41_negated_relational_metamethod#1: negated relational comparison must preserve NaN semantics
-- unluac: expect-contains [[not (]]
-- unluac: expect-contains [[ < ]]
-- unluac: expect-not-contains [[ <= ]]
-- unluac: expect-not-contains [[unluac error]]
-- unluac: expect-ast-count [[function]] [[2]]
-- unluac: expect-ast-count [[if]] [[1]]
-- unluac: expect-ast-max [[local-binding]] [[8]]
-- unluac: expect-ast-count [[local-binding]] [[0]] [[@proto=1]]
-- unluac: expect-ast-count [[local-binding]] [[0]] [[@proto=2]]

local nan = 0 / 0
assert(not (nan < 1))
if nan < 1 then
else
    print("not-lt")
end

local function negated(left, right)
    return not (left < right)
end
assert(negated(nan, 1) == true)
assert(negated(1, nan) == true)
assert(negated(1, 1) == true)
assert(negated(1, 2) == false)
assert(negated(2, 1) == true)
local calls = 0
local trace = ""
local outcome = false
local mt = {
    __lt = function(left, right)
        calls = calls + 1
        trace = trace .. left.tag .. right.tag
        return outcome
    end,
    __le = error,
}
local a = setmetatable({ tag = "a" }, mt)
local b = setmetatable({ tag = "b" }, mt)
assert(negated(a, b) == true)
outcome = 0
assert(negated(a, b) == false)
outcome = ""
assert(negated(a, b) == false)
outcome = nil
assert(negated(a, b) == true)
assert(select("#", negated(a, b)) == 1)
assert(negated(b, a) == true)
assert(calls == 6 and trace == "abababababba")
