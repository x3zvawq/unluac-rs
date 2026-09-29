-- regress_227_while_short_condition_body_backedge#1: while body 不能冒充 repeat 回边 pad
-- unluac: expect-not-contains [[goto ]]
-- unluac: expect-not-contains [[::L]]
-- unluac: expect-not-contains [[unluac error]]
-- unluac: expect-contains [[while (p1_0 or p1_1) and p1_2 do]]
local function run(a, b, c)
    local count = 0
    while (a or b) and c do
        count = count + 1
        a = false
        b = false
    end
    return count
end

local left = run(true, false, true)
local right = run(false, true, true)
local blocked = run(true, true, false)
assert(left == 1 and right == 1 and blocked == 0)
-- 保留前三次直接调用的 O2 展开，再通过原函数观察完整条件的真值边界。
local dispatch = {run}
assert(dispatch[1](nil, false, true) == 0)
assert(dispatch[1](0, false, "") == 1)
assert(dispatch[1](false, "", 0) == 1)
assert(dispatch[1](true, true, nil) == 0)
assert(dispatch[1](nil, nil, 0) == 0)
-- unluac: expect-ast-count [[local-binding]] [[1]] [[@proto=1]]
-- unluac: expect-ast-count [[while]] [[1]] [[@proto=1]]
-- unluac: expect-ast-count [[if]] [[0]] [[@proto=1]]
-- unluac: expect-ast-count [[assign]] [[3]] [[@proto=1]]
print(left, right, blocked)
