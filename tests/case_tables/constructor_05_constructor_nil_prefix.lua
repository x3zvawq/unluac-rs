-- 多目标 nil 声明的逐槽事实由同一构造器候选共享；捕获的 cell 更新仍留在原位。
-- unluac: expect-ast-count [[function]] [[4]]
-- unluac: expect-ast-count [[table-constructor]] [[2]]
-- unluac: expect-ast-max [[local-binding]] [[24]]
-- unluac: expect-ast-count [[local-binding]] [[0]] [[@proto=2]]
-- unluac: expect-ast-count [[local-binding]] [[0]] [[@proto=4]]
-- CALL 的 callee 准备应合回独立初始化，不增加第三条赋值。
-- unluac: expect-ast-max [[assign]] [[2]] [[@proto=3]] [[@dialect=luau]]
local function build()
    local a, b, c, d, e, f, g, h
    local get = function()
        return a + b + c + d + e + f + g + h
    end
    local result = {}
    a = 1
    b = 2
    c = 3
    d = 4
    e = 5
    f = 6
    g = 7
    h = 8
    result.v1 = 1
    result.v2 = 2
    result.v3 = 3
    result.v4 = 4
    result.v5 = 5
    result.v6 = 6
    result.v7 = 7
    result.v8 = 8
    return result, get
end

local result, get = build()
local sum = 0
for i = 1, 8 do sum = sum + result["v" .. i] end
assert(sum == 36 and get() == 36)
print(sum, get())

-- 可调用 initializer 会阻断更早的声明值事实，不能越过它沿用旧的 nil。
local updates = 0
local function barrier()
    local value
    local update = function()
        updates = updates + 1
        value = "updated"
    end
    local ignored = update()
    local result = {}
    value = "final"
    result.value = 9
    return result.value, value, ignored
end
local barrier_result, barrier_value, barrier_ignored = barrier()
assert(barrier_result == 9 and barrier_value == "final" and barrier_ignored == nil)
assert(updates == 1)
assert(select("#", barrier()) == 3 and updates == 2)
print(barrier_result, barrier_value, barrier_ignored)
