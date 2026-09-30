-- 多结果写回已有接收者，其中一个接收者只有未读 nil 初始化；后续清槽必须沿用同一 binding。
-- unluac: expect-ast-max [[local-binding]] [[9]]
-- unluac: expect-ast-count [[function]] [[2]]
-- unluac: expect-ast-max [[assign]] [[6]]
local weak = setmetatable({}, {__mode = "v"})
local next_key = 1
local function pair()
    local first, last = {}, {}
    weak[next_key], weak[next_key + 1] = first, last
    next_key = next_key + 2
    return first, last
end

local function run()
    local first, last = pair()
    collectgarbage("collect")
    assert(weak[1] ~= nil and weak[2] ~= nil)
    first = pair
    local receiver
    receiver, last = first()
    assert(weak[3] ~= nil and weak[4] ~= nil)
    last = nil
    receiver = nil
    collectgarbage("collect")
    assert(weak[3] == nil and weak[4] == nil, "fixed result receiver survived its nil overwrite")
end
run()
assert(next_key == 5)
collectgarbage("collect")
assert(next(weak) == nil)
print("fixed_result_receiver_cleanup", "OK")
