-- 两段与四段模板在 O2 中只展开真条件的首段，完整路径仍保留 CALL。
-- 原 print 顺序及低槽结果均可观察；首次生成即固定展开帧恢复后的声明结构。
local function two(a, b)
    local x = 10
    repeat
        print(x)
        x = x + 2
        print(x)
        if a and b then
            continue
        end
        x = x + 2
        print(x)
        if a and b then
        end
    until a
    return x
end

local function four(a, b)
    local x = -4
    repeat
        print(x)
        x = x + 3
        print(x)
        if a and b then
            continue
        end
        x = x + 3
        print(x)
        if a and b then
            continue
        end
        x = x + 3
        print(x)
        if a and b then
            continue
        end
        x = x + 3
        print(x)
        if a and b then
        end
    until a
    return x
end

local full_two = two(true, false)
assert(full_two == 14)
local early_two = two(true, true)
assert(early_two == 12)
local full_four = four(0, nil)
assert(full_four == 8)
local early_four = four(0, 0)
assert(early_four == -1)
print("repeat_specialized_frame", full_two, early_two, full_four, early_four)

-- unluac: expect-contains [[--!optimize 2]]
-- unluac: expect-ast-count [[local-binding]] [[6]] [[@proto=0]]
-- unluac: expect-ast-count [[assign]] [[0]] [[@proto=0]]
-- unluac: expect-ast-count [[call]] [[9]] [[@proto=0]]
-- unluac: expect-ast-count [[local-binding]] [[1]] [[@proto=1]]
-- unluac: expect-ast-count [[assign]] [[2]] [[@proto=1]]
-- unluac: expect-ast-count [[if]] [[2]] [[@proto=1]]
-- unluac: expect-ast-count [[continue]] [[1]] [[@proto=1]]
-- unluac: expect-ast-count [[local-binding]] [[1]] [[@proto=2]]
-- unluac: expect-ast-count [[assign]] [[4]] [[@proto=2]]
-- unluac: expect-ast-count [[if]] [[4]] [[@proto=2]]
-- unluac: expect-ast-count [[continue]] [[3]] [[@proto=2]]
