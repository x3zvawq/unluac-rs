-- regress_404_method_alias_nested_call_stmt: 稳定receiver不足以提前覆盖SELF的参数槽旧根。
-- unluac: expect-ast-count [[method-call]] [[0]] [[@proto=4]]
-- unluac: expect-ast-count [[method-call]] [[0]] [[@proto=5]]
-- unluac: expect-ast-count [[local-decl]] [[1]] [[@proto=4]]
-- unluac: expect-ast-count [[local-decl]] [[1]] [[@proto=5]]
-- unluac: expect-not-contains [[:m(41)]]
-- unluac: expect-not-contains [[:m(1)]]
-- unluac: expect-ast-count [[local-binding]] [[8]] [[@proto=6]]
-- unluac: expect-ast-count [[local-decl]] [[0]] [[@proto=7]]

local owner = { value = 1 }

function owner:m(delta)
    self.value = self.value + delta
    return self.value
end

local observed
local observed_flag
local function consume(value)
    observed = value
end

local function consume_with_prefix(flag, value)
    observed_flag = flag
    observed = value
end

local function run(sink, source)
    local receiver = source
    sink(receiver.m(receiver, 41))
end

run(consume, owner)
assert(observed == 42, observed)

local function run_with_stable_prefix(sink, source, flag)
    local receiver = source
    sink(not flag, receiver.m(receiver, 1))
end

run_with_stable_prefix(consume_with_prefix, owner, false)
assert(observed_flag == true and observed == 43, observed)
print("regress_404_method_alias_nested_call_stmt", observed)

local weak = setmetatable({}, { __mode = "v" })
local seen_first, seen_last
local function seed()
    -- 两种调用分别在r5/r7写receiver；先在随后复用的调用帧槽留下旧根。
    local a, b, c, d, e, first, f, last = nil, nil, nil, nil, nil, {}, nil, {}
    weak[1], weak[2] = first, last
end
local proxy = setmetatable({}, { __index = function()
    collectgarbage("collect")
    collectgarbage("collect")
    seen_first, seen_last = weak[1] ~= nil, weak[2] ~= nil
    return function(self, delta) return delta end
end })
collectgarbage("stop")
seed()
run(consume, proxy)
assert(seen_first and observed == 41)
seed()
run_with_stable_prefix(consume_with_prefix, proxy, false)
assert(seen_last and observed_flag == true and observed == 1)
collectgarbage("restart")
print("method_receiver_scratch", seen_last, observed)
