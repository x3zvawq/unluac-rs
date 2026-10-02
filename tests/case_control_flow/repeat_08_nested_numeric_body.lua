-- regress_85_repeat_nested_numeric_body#1: nested numeric-for entry is repeat body, not while exit
-- unluac: expect-contains [[repeat]]
-- unluac: expect-contains [[while ]]
-- unluac: expect-contains [[for ]]
-- unluac: expect-contains [[break]]
-- unluac: expect-not-contains [[goto ]]
-- unluac: expect-not-contains [[::L]]
-- unluac: expect-not-contains [[unresolved]]
-- unluac: expect-not-contains [[unluac error]]
-- O2 展开真臂的三轮打印，但不需要为 repeat 的出口增加控制变量。
-- unluac: expect-ast-count [[repeat]] [[1]] [[@proto=1]]
-- unluac: expect-ast-count [[generic-for]] [[1]] [[@proto=1]]
-- unluac: expect-ast-count [[local-binding]] [[3]] [[@proto=1]] [[@variant=O0]]
-- unluac: expect-ast-count [[local-binding]] [[3]] [[@proto=1]] [[@variant=O1]]
-- unluac: expect-ast-count [[local-binding]] [[2]] [[@proto=1]] [[@variant=O2]]
-- unluac: expect-ast-count [[while]] [[1]] [[@proto=2]]
-- unluac: expect-ast-count [[generic-for]] [[1]] [[@proto=2]]
-- unluac: expect-ast-count [[break]] [[1]] [[@proto=2]]
-- 观察器的短路返回不能留下未使用的 false 初始化。
-- unluac: expect-ast-count [[local-binding]] [[0]] [[@proto=4]]
-- 原展开调用须整体恢复，主函数不留下遍历和中转声明。
-- unluac: expect-ast-count [[local-binding]] [[9]] [[@proto=0]]
-- unluac: expect-ast-count [[repeat]] [[0]] [[@proto=0]]
local function run(a, xs)
    for _ in xs do
        repeat
            if a then
                for _ = 1, 3 do
                    print("regress_85_repeat_nested_numeric_body#1 body")
                    continue
                end
                break
            else
                for _ = 1, 3 do
                    print("regress_85_repeat_nested_numeric_body#1 else")
                    print("regress_85_repeat_nested_numeric_body#1 else")
                end
            end
        until a
    end
    return "done"
end

local function keep_while(b, xs)
    while not b do
        for _ in xs do
            continue
        end
        if xs[1] then
            break
        end
    end
    return "while"
end

local repeat_result = run(true, { true })
local while_result = keep_while(true, { true })
assert(repeat_result == "done" and while_result == "while")
local saved_print = print
local calls = 0
local expected = "regress_85_repeat_nested_numeric_body#1 body"
print = function(value)
    assert(value == expected)
    calls = calls + 1
    assert(calls <= 7, "observed repeat backedge")
end
assert(run(0, {true, true}) == "done" and calls == 6)
calls = 0
assert(run(false, {}) == "done" and calls == 0)
expected = "regress_85_repeat_nested_numeric_body#1 else"
assert(not pcall(run, false, {true}))
assert(calls == 8)
print = saved_print
local reads = 0
local probe = setmetatable({}, {
    __index = function(_, key)
        assert(key == 1)
        reads = reads + 1
        assert(reads <= 3)
        return reads == 3 and 0
    end,
})
assert(keep_while(false, probe) == "while" and reads == 3)
reads = 0
assert(keep_while(0, probe) == "while" and reads == 0)
print("regress_85_repeat_nested_numeric_body#1", repeat_result, while_result)
