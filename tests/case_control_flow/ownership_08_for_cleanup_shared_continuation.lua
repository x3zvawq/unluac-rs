-- regress_228_generic_for_cleanup_shared_continuation#1: generic-for Close pad 归一到共享 continuation
-- unluac: expect-not-contains [[goto ]]
-- unluac: expect-not-contains [[::L]]
-- unluac: expect-not-contains [[unluac error]]
-- unluac: expect-ast-min [[generic-for]] [[1]]
local function run(a, b, c, items, value, fallback)
    if (a or b) and c ~= nil then
        for _ in items do
            if value ~= nil then
                return value
            end
        end
    end
    if fallback then
        return fallback
    end
    return 0
end

local calls = 0
local function once(_, control)
    calls = calls + 1
    if control == nil then
        return 1
    end
end

local early = run(true, false, true, once, 7, false)
local fallback = run(false, false, true, once, 7, 9)
assert(early == 7 and fallback == 9)
assert(calls == 1)
calls = 0
assert(run(false, 0, false, once, false, 9) == false and calls == 1)
calls = 0
assert(run(true, false, true, once, nil, "") == "" and calls == 2)
calls = 0
assert(run(true, true, nil, once, 7, 0) == 0 and calls == 0)
assert(run(false, nil, true, once, 7, false) == 0 and calls == 0)
local function empty_iterator()
    calls = calls + 1
end
assert(run("", false, false, empty_iterator, 7, nil) == 0 and calls == 1)
-- unluac: expect-ast-count [[local-binding]] [[7]]
-- unluac: expect-ast-count [[local-binding]] [[6]] [[@proto=0]]
-- 其余五次赋值都属于观察计数器，隐藏迭代槽不应另造 holder 赋值和 nil 清理。
-- unluac: expect-ast-count [[assign]] [[5]]
-- unluac: expect-ast-count [[generic-for]] [[1]]
-- unluac: expect-ast-count [[while]] [[0]]
print(early, fallback)
