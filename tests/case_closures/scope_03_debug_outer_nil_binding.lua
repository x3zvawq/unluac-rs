-- 原 nil 声明的 scope 跨过内层 CLOSE；写入和外层返回必须沿同一绑定，不逐轮补新声明。
local function build()
    local result
    do
        local value = 1
        result = function() return value end
        value = 2
    end
    return result
end

local function choose(first)
    local result
    if first then
        local value = 3
        result = function() return value end
        value = 4
    else
        local value = 5
        result = function() return value end
        value = 6
    end
    return result
end

-- 同 close epoch 的互斥分支各自创建 cell；保存多个激活后再读取，不能误用全局同名槽。
local function independent_cells(first, last)
    local result
    if first then
        local value = 3
        result = function() return value end
        value = last
    else
        local value = 5
        result = function() return value end
        value = last + 1
    end
    return result
end

-- 同形尾部写仍属于各臂的独立 cell，不能按 LocalId 相同而提出到分支之外。
local function equal_cell_tails(first, last)
    local result
    if first then
        local cell = 3
        result = function() return cell end
        cell = last
    else
        local cell = 5
        result = function() return cell end
        cell = last
    end
    return result
end

-- PUC 的 RETURN 可隐式关闭 cell；没有独立 CLOSE 指令也不能共用兄弟分支声明。
local function returned_cell(first, last)
    if first then
        local value = 3
        local result = function() return value end
        value = last
        return result
    else
        local value = 5
        local result = function() return value end
        value = last + 1
        return result
    end
end

-- 未关闭的外层 cell 跨分支和后续 capture 仍共享；不能按各次 reaching Def 拆开。
local function shared_cell(first)
    local value = 1
    local read = function() return value end
    if first then
        value = 2
    else
        value = 3
    end
    local later = function() return value end
    value = 4
    assert(read() == 4 and later() == 4)
end

local function sequential_cell()
    local read, later
    do
        local value = 1
        read = function() return value end
        value = 2
        later = function() return value end
        value = 3
    end
    assert(read() == 3 and later() == 3)
end

-- 同一静态声明每轮在原 CLOSE 后重新激活；所有闭包同时保留再读取。
local function iteration_cells()
    local readers = {}
    for index = 1, 3 do
        local value = index
        readers[index] = function() return value end
        value = value + 10
    end
    assert(readers[1]() == 11 and readers[2]() == 12 and readers[3]() == 13)
end

local function shadow()
    local result
    do
        local result = 9
        print("inner", result)
    end
    result = 10
    return result
end

assert(build()() == 2)
assert(choose(true)() == 4)
assert(choose(false)() == 6)
assert(shadow() == 10)
print("outer-bindings", build()(), choose(true)(), choose(false)())

local old_global_value = value
value = 101
local first_cell = independent_cells(true, 4)
local second_cell = independent_cells(false, 6)
local third_cell = independent_cells(false, 8)
assert(first_cell() == 4 and second_cell() == 7 and third_cell() == 9)
assert(value == 101, "captured branch local overwrote a global sentinel")
value = 102
assert(first_cell() == 4 and second_cell() == 7 and third_cell() == 9)
local equal_first = equal_cell_tails(true, 11)
local equal_second = equal_cell_tails(false, 12)
local equal_third = equal_cell_tails(false, 13)
assert(equal_first() == 11 and equal_second() == 12 and equal_third() == 13)
value = old_global_value
print("independent-cells", first_cell(), second_cell(), third_cell())

shared_cell(true)
shared_cell(false)
sequential_cell()
iteration_cells()

local return_first = returned_cell(true, 4)
local return_second = returned_cell(false, 6)
local return_third = returned_cell(false, 8)
assert(return_first() == 4 and return_second() == 7 and return_third() == 9)

-- 数值循环的控制区只在循环作用域内占槽；内外调用都沿各自原前缀恢复。
do
    local function numeric_frame_scopes(values)
        local order = 0
        local function header(value)
            order = order * 10 + value
            return value
        end
        for index = header(1), header(2), header(1) do
            assert(values[1]() == 1 and values[2]() == 2)
            for inner = 1, 2 do
                assert(values[1]() == 1 and values[2]() == 2)
            end
        end
        assert(order == 121)
        assert(values[1]() == 1 and values[2]() == 2)
    end
    numeric_frame_scopes({ function() return 1 end, function() return 2 end })
end
