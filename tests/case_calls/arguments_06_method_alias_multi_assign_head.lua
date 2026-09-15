-- 普通字段调用保留 lookup 后的 receiver COPY；不能用 SELF 的预写替换。
-- unluac: expect-contains [[.m(]]
-- unluac: expect-ast-count [[method-call]] [[0]] [[@proto=2]]
-- unluac: expect-ast-count [[local-decl]] [[1]] [[@proto=2]]
-- unluac: expect-ast-count [[call]] [[1]] [[@proto=2]]
-- unluac: expect-contains [[p2_2, p2_3 = r2_0.m(r2_0), 9]]
-- unluac: expect-contains [[return p2_2, p2_3]]

local owner = {}

function owner:m()
    return 7, 99
end

local function run(source, enabled, first, second)
    if enabled then
        local receiver = source
        first, second = receiver.m(receiver), 9
    end
    return first, second
end

local first, second = run(owner, true, 0, 0)
assert(first == 7, first)
assert(second == 9, second)
print("regress_408_method_alias_multi_assign_head", first, second)
-- 未进入赋值分支时，两项仍是原参数；不能把写回或常量移到分支外。
first, second = run(owner, false, 41, 43)
assert(first == 41 and second == 43)

-- 原 GETFIELD 查询期间仍持有旧 r6；SELF 会先把该槽覆盖为 receiver。
local weak = setmetatable({}, {__mode = "v"})
local observed = {}
local dynamic_source = setmetatable({}, {__index = function()
    collectgarbage("collect")
    collectgarbage("collect")
    observed[#observed + 1] = type(weak.value)
    return function() return 7, 99 end
end})
local function method(source, enabled, first, second)
    if enabled then
        local receiver = source
        first, second = receiver:m(), 9
    end
    return first, second
end
local function seed(a, b, c, d, e, f, resource)
    weak.value = resource
    return true
end
local function observe(callback)
    do local result = seed(false, false, false, false, false, false, {}) end
    callback(dynamic_source, true, 0, 0)
end
collectgarbage("stop")
observe(run)
observe(method)
collectgarbage("restart")
assert(table.concat(observed, ",") == "table,nil")
