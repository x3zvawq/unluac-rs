-- 条件比较可改写上值，取值叶必须在比较之后重新读取，不能复用谓词的旧快照。
-- unluac: expect-ast-count [[local-binding]] [[0]] [[@proto=1]]
-- unluac: expect-ast-count [[call]] [[1]] [[@proto=1]]
-- unluac: expect-ast-count [[local-binding]] [[0]] [[@proto=2]]
-- unluac: expect-ast-count [[call]] [[1]] [[@proto=2]]
local current, replacement
local gate = true
local calls = 0
local abort = false
local failure = {}
local function check(value, bound)
    assert(value == (current < bound and current or false))
end
local function check_copy(value, bound)
    assert(value == (current < bound and (current or false)))
end
local meta = {__lt = function(left, right)
    calls = calls + 1
    assert(rawequal(left, current) and not rawequal(left, right))
    current = replacement
    if abort then error(failure, 0) end
    return gate
end}
local subject = setmetatable({}, meta)
local bound = setmetatable({}, meta)
local object = {}
local values = {object, 0, "", false}
for index = 1, 5 do
    replacement = values[index]
    current = subject
    check(replacement or false, bound)
    assert(calls == index and rawequal(current, replacement))
end
gate = false
replacement = object
current = subject
check(false, bound)
assert(calls == 6 and rawequal(current, object))
abort = true
current = subject
local ok, problem = pcall(check, object, bound)
assert(not ok and rawequal(problem, failure) and calls == 7)
abort = false
gate = true
replacement = object
current = subject
check_copy(object, bound)
assert(calls == 8 and rawequal(current, object))
replacement = nil
current = subject
check_copy(false, bound)
assert(calls == 9 and current == nil)
gate = false
replacement = object
current = subject
check_copy(false, bound)
assert(calls == 10 and rawequal(current, object))
abort = true
current = subject
ok, problem = pcall(check_copy, object, bound)
assert(not ok and rawequal(problem, failure) and calls == 11)
print("conditional-upvalue-leaf", calls)
