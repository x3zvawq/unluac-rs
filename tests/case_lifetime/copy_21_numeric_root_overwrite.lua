-- 两个副本共享对象，跨回边后由各自原槽的数值写分别退休；提前清除或延迟清除均可观察。
-- unluac: expect-ast-max [[local-binding]] [[3]] [[@proto=1]]
-- unluac: expect-ast-count [[assign]] [[10]] [[@proto=1]]
-- unluac: expect-ast-count [[call]] [[7]] [[@proto=1]]
local weak = setmetatable({}, { __mode = "v" })
local probes = 0
local function run(value, done)
    local first, second
    local armed = false
    ::again::
    first = 0
    collectgarbage("collect")
    assert((weak[1] ~= nil) == armed)
    second = 0.5
    collectgarbage("collect")
    assert(weak[1] == nil)
    assert(first == 0 and second == 0.5)
    probes = probes + 1
    if done then return end
    value = {}
    weak[1] = value
    first = value
    second = value
    value = nil
    collectgarbage("collect")
    assert(weak[1] ~= nil)
    armed = true
    done = true
    goto again
end

run(nil, false)
run(nil, true)
assert(probes == 3 and weak[1] == nil)
print("numeric-root-overwrite", probes)
