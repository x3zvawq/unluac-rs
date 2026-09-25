-- CALL 修改捕获值时，算术仍使用调用前的快照；短路备用值只在原分支写回。
-- unluac: expect-contains [[value = value + (provider:next() or 1)]] [[@debug=retained]]
-- unluac: expect-contains [[value = value + (provider:next() and 2)]] [[@debug=retained]]
-- unluac: expect-ast-count [[local-binding]] [[7]] [[@proto=0]]
-- unluac: expect-ast-count [[local-binding]] [[0]] [[@proto=1]]
-- unluac: expect-ast-count [[local-binding]] [[0]] [[@proto=2]]
-- unluac: expect-ast-count [[local-binding]] [[0]] [[@proto=3]]
local value = 10
local provider
-- vararg 保留独立调用边界，避免 O2 把调用点展开成另一套捕获值读写布局。
local function update(...)
    value = value + (provider:next() or 1)
    return value
end
local function update_and(...)
    value = value + (provider:next() and 2)
    return value
end
local calls = 0
local result = 3
provider = {next = function(self)
    assert(self == provider)
    calls = calls + 1
    value = 1000
    return result
end}
assert(update() == 13)
result = false
assert(update() == 14)
result = nil
assert(update() == 15)
result = 0
assert(update() == 15)
result = true
assert(update_and() == 17)
result = false
local ok = pcall(update_and)
assert(not ok and value == 1000 and calls == 6)
print("captured-call-selection", value, calls, ok)
