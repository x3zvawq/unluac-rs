-- Luau 的 while continue 跳到入口，repeat continue 则必须求值尾条件。
-- O2 内联 tail 后的 true/false 物化也应归还尾条件，不能把赋值臂的合流跳转当成 continue。
-- unluac: expect-ast-count [[continue]] [[0]] [[@proto=1]]
-- unluac: expect-ast-min [[while]] [[1]]
-- unluac: expect-ast-min [[repeat]] [[1]]
-- unluac: expect-ast-count [[while]] [[1]] [[@proto=1]]
-- unluac: expect-ast-count [[repeat]] [[1]] [[@proto=1]]
-- unluac: expect-ast-count [[if]] [[3]] [[@proto=1]]
-- unluac: expect-ast-count [[empty-local]] [[0]] [[@proto=1]]
-- unluac: expect-not-contains [[goto ]]
-- unluac: expect-not-contains [[unresolved]]
-- unluac: expect-not-contains [[unluac error]]
-- 父函数直接绑定两组三结果；断言实参不再拆成 callee、参数和结果接棒。
-- unluac: expect-ast-count [[local-binding]] [[16]] [[@proto=0]]
-- unluac: expect-ast-count [[assign]] [[0]] [[@proto=0]]
-- O2 展开 oracle 的第二轮后仍保留一次 skip 检查，即使两个出口相同也不能删除原分支。
-- unluac: expect-instruction-count [[branch]] [[5]] [[@proto=3]] [[@variant=O2]]
-- 嵌套调用准备应完整进入 until，保留 debug 也不增加跨轮 callee carrier。
-- unluac: expect-ast-count [[repeat]] [[1]] [[@proto=6]]
-- unluac: expect-ast-count [[empty-local]] [[0]] [[@proto=6]]
-- unluac: expect-ast-count [[repeat-condition-local]] [[0]] [[@proto=6]] [[@variant=O0]]
-- unluac: expect-ast-count [[repeat-condition-local]] [[0]] [[@proto=6]] [[@variant=O1]]
-- 循环状态直接初始化；每轮快照必须在分支内独立声明，不能使用清零的共享 cell。
-- unluac: expect-ast-count [[empty-local]] [[0]] [[@proto=7]]
-- unluac: expect-ast-count [[repeat]] [[1]] [[@proto=7]]
-- unluac: expect-ast-count [[if]] [[1]] [[@proto=7]]
-- unluac: expect-ast-count [[repeat-condition-local]] [[0]] [[@proto=7]]
local function observe(skip, stop)
    local trace = {}
    local i, total = 0, 0
    local function tail(j)
        trace[#trace + 1] = i * 10 + j
        return j == 2
    end
    while i < 4 do
        i = i + 1
        if skip and i % 2 == 0 then
            continue
        end
        local j = 0
        repeat
            j = j + 1
            if skip and j == 1 then
                continue
            end
            total = total + i * 10 + j
        until tail(j)
        if stop and i == 3 then
            break
        end
    end
    return total, table.concat(trace, ","), i
end

local function expected(skip, stop)
    local trace, total = {}, 0
    local last = stop and 3 or 4
    for i = 1, last do
        if not skip or i % 2 ~= 0 then
            for j = 1, 2 do
                if not skip or j ~= 1 then
                    total = total + i * 10 + j
                end
                trace[#trace + 1] = i * 10 + j
            end
        end
    end
    return total, table.concat(trace, ","), last
end

for mode = 0, 3 do
    local skip, stop = mode % 2 == 1, mode >= 2
    local value, trace, last = observe(skip, stop)
    local want_value, want_trace, want_last = expected(skip, stop)
    assert(value == want_value)
    assert(trace == want_trace)
    assert(last == want_last)
    print("luau_03#1", mode, value, trace, last)
end

-- O2 将 helper 内联并物化比较结果；恢复 until 时必须每轮只调用一次 __eq。
local compared = {}
local comparison_mt = {
    __eq = function(left, right)
        compared[#compared + 1] = left.value
        return left.value == right.value
    end,
}
local function same(left, right)
    return left == right
end
local function compare_until(limit)
    local iteration = 0
    local target = setmetatable({ value = limit }, comparison_mt)
    repeat
        iteration = iteration + 1
    until same(setmetatable({ value = iteration }, comparison_mt), target)
    return iteration
end
assert(compare_until(3) == 3)
assert(table.concat(compared, ",") == "1,2,3")
print("repeat comparison calls", table.concat(compared, ","))

-- 提前 continue 必须读取上一轮 callee，不能将真实 carried 状态当成本轮准备退休。
local function carry_until(skip_at)
    local iteration = 0
    local probe = function() return false end
    repeat
        iteration = iteration + 1
        assert(iteration <= 3)
        if iteration == skip_at then continue end
        local snapshot = iteration
        probe = function() return snapshot >= 2 end
    until probe()
    return iteration
end
assert(carry_until(0) == 2)
assert(carry_until(1) == 2)
assert(carry_until(2) == 3)
