-- regress_82_numeric_for_control_pad#1: a reachable numeric latch exit pad is loop control
-- unluac: expect-contains [[for ]]
-- unluac: expect-contains [[while ]]
-- unluac: expect-not-contains [[goto ]]
-- unluac: expect-not-contains [[unresolved]]
-- unluac: expect-not-contains [[unluac error]]
-- unluac: expect-not-contains [[(function()]]
-- 迭代器副本已有支配全部读取与退休点的初始化，不应提前补入口 nil。
-- unluac: expect-max-count [[ = nil]] [[0]] [[@variant=O2]]
-- O2 将固定三轮 numeric-for 展开，三个 while 仍须归属外层 generic-for。
-- unluac: expect-ast-count [[generic-for]] [[1]] [[@proto=1]]
-- unluac: expect-ast-count [[numeric-for]] [[1]] [[@proto=1]] [[@variant=O0]]
-- unluac: expect-ast-count [[numeric-for]] [[1]] [[@proto=1]] [[@variant=O1]]
-- unluac: expect-ast-count [[numeric-for]] [[0]] [[@proto=1]] [[@variant=O2]]
-- unluac: expect-ast-count [[while]] [[1]] [[@proto=1]] [[@variant=O0]]
-- unluac: expect-ast-count [[while]] [[1]] [[@proto=1]] [[@variant=O1]]
-- unluac: expect-ast-count [[while]] [[3]] [[@proto=1]] [[@variant=O2]]
-- unluac: expect-ast-count [[local-binding]] [[2]] [[@proto=1]] [[@variant=O0]]
-- unluac: expect-ast-count [[local-binding]] [[2]] [[@proto=1]] [[@variant=O1]]
-- unluac: expect-ast-count [[local-binding]] [[1]] [[@proto=1]] [[@variant=O2]]
-- 原尾检查仍须执行；不能把条件 continue 降成空 if。
-- unluac: expect-ast-count [[continue]] [[1]] [[@proto=1]] [[@variant=O0]]
-- unluac: expect-ast-count [[continue]] [[1]] [[@proto=1]] [[@variant=O1]]
-- unluac: expect-ast-count [[continue]] [[3]] [[@proto=1]] [[@variant=O2]]
-- 共享回边的两个短路项须组成完整 OR，不留下反向 branch-around。
-- unluac: expect-count [[ or ]] [[2]] [[@variant=O0]]
-- unluac: expect-count [[ or ]] [[2]] [[@variant=O1]]
-- unluac: expect-count [[ or ]] [[4]] [[@variant=O2]]
-- 尾 nil 与原位全局写回均不阻断完整帧；旧表声明结束后，断言及调用准备不再接棒。
-- unluac: expect-ast-max [[assign]] [[5]] [[@proto=0]] [[@variant=O2]]
-- unluac: expect-ast-max [[local-binding]] [[10]] [[@proto=0]] [[@variant=O2]]
-- unluac: expect-max-count [[ = assert]] [[0]] [[@variant=O2]]
local function run(a, b, c, xs)
    for _ in xs do
        print("regress_82_numeric_for_control_pad#1 body")
        for _ = 1, 3 do
            while b do
                if a or c then
                    continue
                end
            end
        end
        continue
    end
end

run(false, false, false, { 1 })
local saved_print = print
local visits = 0
print = function(value)
    assert(value == "regress_82_numeric_for_control_pad#1 body")
    visits = visits + 1
end
run(false, false, true, { 1, 2, 3 })
assert(visits == 3)
visits = 0
run(true, false, false, { 1, 2 })
assert(visits == 2)
visits = 0
run(nil, true, false, {})
assert(visits == 0)
run(0, nil, "", { 1 })
assert(visits == 1)
print = saved_print

-- 原 run 的非空 b=true 路径不终止；有限同构尾检查实际观察短路调用和回边次数。
-- unluac: expect-ast-count [[while]] [[1]] [[@proto=3]]
-- unluac: expect-ast-count [[continue]] [[1]] [[@proto=3]]
-- unluac: expect-ast-count [[call]] [[1]] [[@proto=3]]
local function finite(a, next_value, limit)
    local n = 0
    while n < limit do
        n = n + 1
        if a or next_value(n) then
            continue
        end
    end
    return n
end

local calls = 0
local function observe(n)
    calls = calls + 1
    assert(n == calls)
    if n % 2 == 0 then return false end
    return 0
end
local dispatch = { finite }
assert(dispatch[1](true, observe, 4) == 4)
assert(dispatch[1](0, observe, 4) == 4)
assert(dispatch[1]("", observe, 4) == 4)
assert(calls == 0)
assert(dispatch[1](false, observe, 4) == 4)
assert(calls == 4)
calls = 0
assert(dispatch[1](nil, observe, 5) == 5)
assert(calls == 5)
print("numeric control pad tail", calls)
