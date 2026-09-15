-- regress_131_lua55_anonymous_vararg#1: PF_VAHID 不能伪装成命名变参
-- unluac: expect-contains [[(...)]]
-- unluac: expect-not-contains [[(...r]]
-- unluac: expect-ast-count [[named-vararg-function]] [[0]]
local subject = function(...)
    return ...
end

assert(select("#", subject()) == 0)
assert(select("#", subject(nil)) == 1)
local token = {}
local a, b, c, d = subject(token, nil, false, nil)
assert(a == token and b == nil and c == false and d == nil)
assert(select("#", subject(token, nil, false, nil)) == 4)
print("regress_131#1", select("#", subject(token, nil, false, nil)), b, c, d)
