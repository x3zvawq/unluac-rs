-- CALL 先写回捕获 cell，随后同槽创建的闭包由后续有返回值的调用消费。
-- unluac: expect-ast-count [[local-function]] [[1]] [[@proto=0]]
local receiver
local lookups = 0
receiver = setmetatable({}, {__index = function(old, key)
    assert(key == "absent")
    lookups = lookups + 1
    receiver = {}
    return old
end})
local function choose(expected)
    if expected == receiver then return true end
    return false
end
assert(choose(receiver))
assert(not choose({}))
local original = receiver
local observed = receiver.absent
assert(observed == original and receiver ~= original and lookups == 1)
assert(not choose(original) and choose(receiver))
print("writeback-before-callable", lookups, choose(receiver))
