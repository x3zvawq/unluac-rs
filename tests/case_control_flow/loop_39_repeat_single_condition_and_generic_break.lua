-- regress_92_repeat_single_condition_and_generic_break#1: one-node repeat condition must survive early continue/break
-- regress_92_repeat_single_condition_and_generic_break#2: generic-for body==exit means immediate break, not empty body
-- unluac: expect-contains [[repeat]]
-- unluac: expect-contains [[for ]]
-- unluac: expect-contains [[break]]
-- unluac: expect-contains [[continue]]
-- unluac: expect-not-contains [[goto ]]
-- unluac: expect-not-contains [[::L]]
-- unluac: expect-not-contains [[unresolved]]
-- unluac: expect-not-contains [[unluac error]]
-- unluac: expect-not-contains [[in function()]]
local function repeat_single_condition(a, xs)
    repeat
        if a then
            if xs[0] then
                break
            end
            continue
        end
    until a
    return 1
end

local function generic_immediate_break()
    local calls = 0
    local function iter()
        calls = calls + 1
        if calls == 1 then
            return calls
        end
    end
    for _ in iter do
        break
    end
    return calls
end

local function repeat_prefix_continue()
    local rounds = 0
    local probes = 0
    local function probe(value)
        probes = probes + 1
        return value
    end
    repeat
        rounds = rounds + 1
        if rounds == 1 then
            continue
        end
        if probe(false) then
            continue
        end
        if probe(true) then
            break
        end
    until rounds > 3
    return rounds, probes
end

local repeat_result = repeat_single_condition(true, { [0] = false })
local iterator_calls = generic_immediate_break()
local rounds, probes = repeat_prefix_continue()
assert(repeat_result == 1)
assert(iterator_calls == 1)
assert(rounds == 2 and probes == 2)
print("regress_92_repeat_single_condition_and_generic_break#1", repeat_result)
print("regress_92_repeat_single_condition_and_generic_break#2", iterator_calls)
print("regress_92_repeat_single_condition_and_generic_break#3", rounds, probes)
-- 表分派保留 O2 下的被测函数调用；真值条件分别走 break 和 continue 后的尾条件。
do
    local dispatch = {repeat_single_condition}
    assert(dispatch[1](true, {[0] = true}) == 1)
    assert(dispatch[1](0, {[0] = 0}) == 1)
    assert(dispatch[1]("", {[0] = ""}) == 1)
    assert(dispatch[1](true, {}) == 1)
    local reads = 0
    assert(dispatch[1](0, setmetatable({}, {__index = function(_, key)
        reads = reads + 1
        assert(key == 0)
        return false
    end})) == 1)
    assert(reads == 1)
end
-- probe 的 O2 内联仍须复用原 probes 状态，不留下出口或常量判定 carrier。
-- unluac: expect-ast-count [[local-binding]] [[3]] [[@proto=4]]
-- unluac: expect-ast-count [[local-binding]] [[0]] [[@proto=1]]
-- unluac: expect-ast-count [[repeat]] [[1]] [[@proto=1]]
-- unluac: expect-ast-count [[if]] [[2]] [[@proto=1]]
-- unluac: expect-ast-count [[break]] [[1]] [[@proto=1]]
-- unluac: expect-ast-count [[local-binding]] [[3]] [[@proto=2]]
-- unluac: expect-ast-count [[generic-for]] [[1]] [[@proto=2]]
-- unluac: expect-ast-count [[break]] [[1]] [[@proto=2]]
-- unluac: expect-ast-count [[local-binding]] [[0]] [[@proto=3]]
-- unluac: expect-ast-count [[local-binding]] [[0]] [[@proto=5]]
-- unluac: expect-ast-count [[local-binding]] [[9]] [[@proto=0]] [[@variant=O0]]
-- unluac: expect-ast-count [[local-binding]] [[9]] [[@proto=0]] [[@variant=O1]]
-- unluac: expect-ast-count [[local-binding]] [[13]] [[@proto=0]] [[@variant=O2]]

-- 未展开的完整调用链保留所有观察调用，不留下 callee/result 重赋值。
-- unluac: expect-ast-count [[call]] [[21]] [[@proto=0]] [[@variant=O0]]
-- unluac: expect-ast-count [[call]] [[21]] [[@proto=0]] [[@variant=O1]]
-- unluac: expect-ast-count [[assign]] [[0]] [[@proto=0]] [[@variant=O0]]
-- unluac: expect-ast-count [[assign]] [[0]] [[@proto=0]] [[@variant=O1]]

-- 捕获状态沿各出口使用同一 cell，不生成重复的空暂存声明。
-- unluac: expect-ast-count [[empty-local]] [[0]] [[@proto=4]]
