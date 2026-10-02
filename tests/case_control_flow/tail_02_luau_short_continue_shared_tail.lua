-- regress_111_luau_short_continue_shared_tail#1: 短路 continue 与 break 共享本轮 for tail
-- unluac: expect-contains [[for ]]
-- unluac: expect-contains [[repeat]]
-- unluac: expect-contains [[    continue]]
-- continue 臂可翻转为 De Morgan 条件，仍须保留两个原操作数。
-- unluac: expect-contains [[not p1_0 and not p1_2]]
-- unluac: expect-count [[p1_0 and p1_1]] [[2]]
-- unluac: expect-not-contains [[goto ]]
-- unluac: expect-not-contains [[::L]]
-- unluac: expect-not-contains [[unresolved]]
-- unluac: expect-not-contains [[unluac error]]
-- O2 已展开三轮 numeric-for，但共享 x 不应随展开产生新的状态绑定。
-- unluac: expect-ast-count [[numeric-for]] [[0]] [[@proto=1]]
-- unluac: expect-ast-count [[repeat]] [[3]] [[@proto=1]]
-- unluac: expect-ast-count [[generic-for]] [[1]] [[@proto=1]]
-- unluac: expect-ast-count [[local-binding]] [[3]] [[@proto=1]]
-- unluac: expect-ast-count [[local-binding]] [[3]] [[@proto=3]]
-- unluac: expect-ast-count [[repeat]] [[3]] [[@proto=3]]
-- unluac: expect-ast-count [[continue]] [[1]] [[@proto=3]]
-- unluac: expect-ast-count [[break]] [[1]] [[@proto=3]]
-- 展开调用与整个后缀共同恢复，根函数只保留源码绑定和输入矩阵遍历。
-- unluac: expect-ast-count [[local-binding]] [[6]] [[@proto=0]]
-- unluac: expect-ast-count [[generic-for]] [[1]] [[@proto=0]]
local function run(a, b, c, xs)
    local x = 0
    for k, v in xs do
        if a then
            for i = 1, 3 do
                x = x + 1
                repeat
                    x = x + 1
                until b
            end
        else
            if a or c then
                if a and b then
                    x = x + 1
                end
            else
                x = x + 1
                continue
            end
            if a and b then
                print(x)
                if xs[x] then
                    break
                end
            end
        end
        x = x + 1
    end
    return x
end

print("regress_111_result", run(false, true, false, {}), run(false, true, false, { 1 }), run(false, true, true, { 1 }))

-- 从表中读取参数，实际执行保留检查后的两臂和共享 tail。
for _, input in {{false, false, 1}, {false, true, 1}, {true, false, 7}} do
    assert(run(input[1], true, input[2], {1}) == input[3])
end

local subjects = { run }
local xs = setmetatable({ 1, 2 }, { __index = function()
    error("unselected lookup")
end })
assert(subjects[1](false, false, false, xs) == 2)
assert(subjects[1](nil, nil, 0, xs) == 2)
assert(subjects[1](0, "", false, xs) == 14)
assert(subjects[1]("", 0, true, xs) == 14)
assert(subjects[1](true, false, nil, {}) == 0)

-- 外层条件独立后，内层更新与共享 tail 都能实际执行；不能让正常臂落入 continue。
local function independent(outer, a, b, c, values)
    local x = 0
    for _, value in values do
        if outer then
            for i = 1, 3 do
                x = x + 1
                repeat
                    x = x + 1
                until b
            end
        else
            if a or c then
                if a and b then
                    x = x + 1
                end
            else
                x = x + 1
                continue
            end
            if a and b then
                print(x)
                if values[x] then
                    break
                end
            end
        end
        x = x + 1
    end
    return x
end
subjects[2] = independent
assert(subjects[2](false, true, true, false, {false, false}) == 4)
assert(subjects[2](false, true, true, false, {true, false}) == 1)
assert(subjects[2](false, false, false, false, {false, false}) == 2)
assert(subjects[2](false, false, false, true, {false, false}) == 2)
assert(subjects[2](true, false, true, false, {false, false}) == 14)
