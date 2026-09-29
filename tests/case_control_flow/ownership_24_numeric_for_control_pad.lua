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
