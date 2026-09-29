-- 循环 header 是条件臂的完成边界，另一臂的尾部动作仍必须受条件控制。
-- unluac: expect-ast-min [[if]] [[5]] [[@proto=1]] [[@dialect=lua5.1]]
-- 循环尾部的短路写回仍属于当前条件臂，不应退化成标签和 goto。
-- unluac: expect-ast-count [[goto]] [[0]]
-- unluac: expect-ast-count [[label]] [[0]]
-- PUC 5.4/5.5 的 TESTSET 仍保留 state 与常量的测试，回边值直接写回参数。
-- unluac: expect-ast-count [[local-decl]] [[1]] [[@proto=5]] [[@dialect=lua5.4]]
-- unluac: expect-ast-count [[local-decl]] [[1]] [[@proto=5]] [[@dialect=lua5.5]]
-- unluac: expect-contains [[state and 2]] [[@debug=retained]] [[@dialect=lua5.4]]
-- unluac: expect-contains [[state and 2]] [[@debug=retained]] [[@dialect=lua5.5]]
-- 根函数只保留源码绑定；并行重置不能留下影响后续调用和 scores 构造的 scratch。
-- unluac: expect-ast-count [[local-decl]] [[6]] [[@proto=0]] [[@debug=stripped]]
-- unluac: expect-ast-count [[local-decl]] [[7]] [[@proto=0]] [[@debug=retained]]
-- unluac: expect-count [[checks, actions = {}, {}]] [[2]] [[@debug=retained]] [[@dialect=lua5.1]]
-- unluac: expect-count [[checks, actions = {}, {}]] [[2]] [[@debug=retained]] [[@dialect=luajit]]

local function worker()
    while true do
        coroutine.yield()
        if enabled() then
            if accepts(1) then
                record(1)
            elseif accepts(2) then
                record(2)
            elseif accepts(3) then
                record(3)
            else
                if not accepts(4) then
                    record(4)
                end
            end
        end
    end
end

local selected, active = 0, true
local checks, actions = {}, {}
function enabled() return active end
function accepts(index)
    checks[#checks + 1] = index
    return selected == index
end
function record(index) actions[#actions + 1] = index end

local thread = coroutine.create(worker)
assert(coroutine.resume(thread))
for index = 0, 4 do
    selected = index
    checks, actions = {}, {}
    assert(coroutine.resume(thread))
    local expected = index == 0 and 4 or index
    assert(#checks == expected)
    for i = 1, expected do assert(checks[i] == i) end
    if index == 4 then
        assert(#actions == 0)
    else
        assert(#actions == 1 and actions[1] == expected)
    end
    print('branch-tail', index, #checks, #actions)
end
active = false
checks, actions = {}, {}
assert(coroutine.resume(thread))
assert(#checks == 0 and #actions == 0)

-- 短路结果的两个出口均回到循环头；不能将早回边当作顺序落入 nil 分支。
local function loop_value_frontier(state)
    local visits = 0
    while state do
        visits = visits + 1
        if state == 1 then
            state = state and 2 or nil
        else
            state = nil
        end
    end
    return visits
end
assert(loop_value_frontier(1) == 2)
assert(loop_value_frontier(2) == 1)
assert(loop_value_frontier(nil) == 0)
assert(loop_value_frontier(false) == 0)
assert(loop_value_frontier(true) == 1)
assert(loop_value_frontier(0) == 1)
assert(loop_value_frontier("") == 1)

-- generic-for 尾块只有一条字段写，也不是纯 Jump 的 continue 垫块。
-- rank 调整和 brag 标记有不同条件，字段写不能跨出所属短路条件臂。
local function update_ranks(scores, new_index, old_index)
    for i, v in ipairs(scores) do
        if old_index <= i then v.rank = v.rank - 1 end
        if new_index <= i then v.rank = v.rank + 1 end
        if new_index <= i and i < old_index and not v.isBot and v.points > 0 then
            v.brag = true
        end
    end
end

local scores = {
    {rank = 1, points = 1},
    {rank = 2, points = 1},
    {rank = 3, points = 0},
    {rank = 4, points = 1, isBot = true},
}
update_ranks(scores, 2, 4)
assert(scores[1].brag == nil and scores[2].brag == true)
assert(scores[3].brag == nil and scores[4].brag == nil)
assert(scores[1].rank == 1 and scores[2].rank == 3)
assert(scores[3].rank == 4 and scores[4].rank == 4)
for index, score in ipairs(scores) do
    print("guarded-tail-write", index, score.rank, score.brag)
end
