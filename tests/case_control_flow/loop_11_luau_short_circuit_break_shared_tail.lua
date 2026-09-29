-- regress_158_luau_short_circuit_break_shared_tail#1: 短路一臂经 guard break，另一臂直达共享 tail
-- unluac: expect-contains [[repeat]]
-- unluac: expect-not-contains [[not p1_0 and]]
-- unluac: expect-not-contains [[goto ]]
-- unluac: expect-not-contains [[::L]]
-- unluac: expect-not-contains [[unresolved]]
-- unluac: expect-not-contains [[unluac error]]
local function run(a, b, c, xs)
    local x = 0
    repeat
        if not a then
            repeat
                if not (a or not a and (not c and a or c)) then
                    break
                end
                print(x)
                if xs[x] then
                    break
                end
                if a and b then
                    x += 1
                end
                for _ in xs, nil, nil do
                    x += 1
                    x += 1
                end
                if xs[x] then
                    break
                end
                print(x)
            until xs[x]
        end
    until a or c
    return x
end

print("regress_158_luau_short_circuit_break_shared_tail#1", run(true, true, false, {}))
assert(run(false, true, true, {[0] = true}) == 0)

local dispatch = {run}
assert(dispatch[1](true, false, false, {}) == 0)
assert(dispatch[1](false, false, true, {[2] = true}) == 2)
assert(dispatch[1](false, true, true, {[2] = true, [4] = true}) == 4)
assert(dispatch[1](0, nil, false, {}) == 0)
assert(dispatch[1](nil, 0, 0, {[2] = true}) == 2)
-- 首部、共享尾和 until 分别读取同一槽；第三次读取才退出。
local reads = 0
local values = setmetatable({}, {__index = function(_, key)
    assert(key == 0)
    reads = reads + 1
    return reads == 3
end})
assert(dispatch[1](false, false, true, values) == 0)
assert(reads == 3)

local saved_print, stop, trace = print, {}, {}
print = function(value)
    trace[#trace + 1] = value
    if #trace == 3 then error(stop) end
end
local ok, failure = pcall(dispatch[1], false, true, true, {true, true})
print = saved_print
assert(not ok and failure == stop)
assert(#trace == 3 and trace[1] == 0 and trace[2] == 4 and trace[3] == 4)
print("observed_shared_tail", reads, trace[1], trace[2], trace[3])
-- a/c 同为假时原程序无观察点且不终止，不执行该输入。
-- unluac: expect-ast-count [[repeat]] [[2]] [[@proto=1]]
-- unluac: expect-ast-count [[generic-for]] [[1]] [[@proto=1]]
-- unluac: expect-ast-count [[while]] [[0]] [[@proto=1]]
-- 原分派表和闭包捕获不应给主函数引入 callee、比较结果或参数别名。
-- unluac: expect-ast-count [[local-binding]] [[9]] [[@proto=0]]
-- unluac: expect-ast-count [[call]] [[22]] [[@proto=0]]
-- guard 的重复测试来自原指令；保留分层短路、共享尾及各次打印。
-- unluac: expect-ast-count [[local-binding]] [[2]] [[@proto=1]]
-- unluac: expect-ast-count [[assign]] [[2]] [[@proto=1]]
-- unluac: expect-ast-count [[if]] [[7]] [[@proto=1]]
-- unluac: expect-ast-count [[break]] [[4]] [[@proto=1]]
-- unluac: expect-ast-count [[call]] [[2]] [[@proto=1]]
