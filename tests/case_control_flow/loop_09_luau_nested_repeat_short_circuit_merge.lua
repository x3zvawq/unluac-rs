-- regress_151_luau_nested_repeat_short_circuit_merge#1: 短路链尾与 plain if-then 共享本轮 merge
-- unluac: expect-contains [[repeat]]
-- unluac: expect-contains [[not (p1_0 or p1_2)]]
-- unluac: expect-not-contains [[goto ]]
-- unluac: expect-not-contains [[::L]]
-- unluac: expect-not-contains [[unresolved]]
-- unluac: expect-not-contains [[unluac error]]
local function run(a, b, c, xs)
    local x = 0
    repeat
        if not a then
            local done
            repeat
                if not (a or c) then
                    if not (a or c) then
                        break
                    end
                    print(x)
                    done = xs[x]
                    if done then
                        break
                    end
                end
                if a and b then
                    x += 1
                end
                for _ in xs do
                    x += 1
                    x += 1
                end
                if xs[x] then
                    break
                end
                print(x)
                done = xs[x]
            until done
        end
    until a or c
    return x
end

print("regress_151_luau_nested_repeat_short_circuit_merge#1", run(true, true, false, {}))

local dispatch = {run}
assert(dispatch[1](true, false, false, {}) == 0)
assert(dispatch[1](false, false, true, {[2] = true}) == 2)
assert(dispatch[1](false, true, true, {[2] = true, [4] = true}) == 4)
assert(dispatch[1](0, nil, false, {}) == 0)
assert(dispatch[1](nil, 0, 0, {[2] = true}) == 2)
local reads = 0
local values = setmetatable({}, {__index = function(_, key)
    assert(key == 0)
    reads = reads + 1
    return reads == 2
end})
assert(dispatch[1](false, false, true, values) == 0)
assert(reads == 2)

local saved_print, stop, trace = print, {}, {}
print = function(value)
    trace[#trace + 1] = value
    if #trace == 3 then error(stop) end
end
local ok, failure = pcall(dispatch[1], false, true, true, {true, true})
print = saved_print
assert(not ok and failure == stop)
assert(#trace == 3 and trace[1] == 4 and trace[2] == 8 and trace[3] == 12)
print("observed_inner_repeat", reads, trace[1], trace[2], trace[3])
-- a/c 同时为假时，原外层循环没有观察点且不终止，保留其字节码结构，不执行该输入。
-- unluac: expect-ast-count [[repeat]] [[2]] [[@proto=1]]
-- unluac: expect-ast-count [[generic-for]] [[1]] [[@proto=1]]
-- unluac: expect-ast-count [[while]] [[0]] [[@proto=1]]
-- 构造器 buffer 与后续被捕获的表复用原调用槽，不应留下调用结果或 assert 别名。
-- unluac: expect-ast-count [[local-binding]] [[9]] [[@proto=0]]
-- unluac: expect-ast-count [[call]] [[20]] [[@proto=0]]
-- 原 done 的 nil 初始化仍保留；两个 repeat、显式检查和各次打印不能消失。
-- unluac: expect-ast-count [[local-binding]] [[3]] [[@proto=1]]
-- unluac: expect-ast-count [[assign]] [[2]] [[@proto=1]]
-- unluac: expect-ast-count [[if]] [[6]] [[@proto=1]]
-- unluac: expect-ast-count [[break]] [[3]] [[@proto=1]]
-- unluac: expect-ast-count [[call]] [[2]] [[@proto=1]]
