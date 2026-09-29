-- regress_110_luau_generic_for_exit_break_pad#1: generic-for exit 透明 pad 汇入立即 break body
-- unluac: expect-contains [[while ]]
-- unluac: expect-contains [[for ]]
-- unluac: expect-contains [[                    break]]
-- unluac: expect-not-contains [[goto ]]
-- unluac: expect-not-contains [[::L]]
-- unluac: expect-not-contains [[unresolved]]
-- unluac: expect-not-contains [[unluac error]]
local function run(a, state, probe, xs)
    local x = 0
    while not state.done do
        repeat
            if a then
                if probe[x] then
                    break
                end
                for k, v in xs do
                    break
                end
            else
                x = x + 1
            end
            break
        until state.done
    end
    return x
end

local calls = 0
local state = { done = false }
local function iterator()
    calls = calls + 1
    if calls <= 2 then
        state.done = true
        return calls, calls
    end
end

local result = run(true, state, {}, iterator)
print("regress_110_luau_generic_for_exit_break_pad#1", result, calls)
assert(result == 0 and calls == 1)
-- false 分支由外层条件的读取次数终止，repeat 的立即 break 不多读 done。
calls = 0
-- 间接调用让 O2 继续执行原 subject，而不把常量分支展开进观察代码。
local dispatch = {run}
local reads = 0
local proxy = setmetatable({}, {__index = function(_, key)
    assert(key == "done")
    reads = reads + 1
    return reads > 3
end})
assert(dispatch[1](false, proxy, {}, iterator) == 3 and reads == 4 and calls == 0)
-- probe 的真值直接退出 repeat，不能进入 generic-for。
state.done = false
reads = 0
proxy = setmetatable({}, {__index = function(_, key)
    assert(key == 0)
    reads = reads + 1
    state.done = true
    return 0
end})
assert(dispatch[1]("", state, proxy, iterator) == 0 and reads == 1 and calls == 0)
local function empty_iterator()
    calls = calls + 1
    state.done = true
end
state.done = false
assert(dispatch[1](0, state, {}, empty_iterator) == 0 and calls == 1)
assert(dispatch[1](true, state, proxy, iterator) == 0 and calls == 1 and reads == 1)
-- unluac: expect-ast-count [[local-binding]] [[12]]
-- unluac: expect-ast-count [[local-binding]] [[9]] [[@proto=0]]
-- O2 展开主体后，后继断言仍须恢复完整调用，不能逐轮增加 callee 别名。
-- unluac: expect-max-count [[ = assert]] [[0]]
-- unluac: expect-ast-count [[while]] [[1]]
-- unluac: expect-ast-count [[generic-for]] [[1]]
-- unluac: expect-ast-count [[repeat]] [[0]]
-- unluac: expect-ast-count [[break]] [[1]]
