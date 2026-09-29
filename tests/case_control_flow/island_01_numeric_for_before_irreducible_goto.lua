-- regress_182_numeric_for_before_irreducible_goto#1: 局部不可规约流不得拖垮前置 numeric-for
-- unluac: expect-contains [[for ]]
-- unluac: expect-not-contains [[unluac error]]
-- unluac: expect-not-contains [[unresolved]]
-- The shared literal must remain materialized before the irreducible region; its local ID is not stable.
-- unluac: expect-contains [[ = "prefix"]]
-- unluac: expect-order [[ = "prefix"]] [[goto ]]

local function prefix_before_irreducible(entry, cycle)
    local prefix = "prefix"
    print(prefix)
    print(prefix)

    local value = 0
    if entry then
        goto second
    end
    ::first::
    value = value + 1
    ::second::
    value = value + 10
    if cycle then
        goto first
    end
    return value
end

assert(prefix_before_irreducible(true, false) == 10)
assert(prefix_before_irreducible(false, false) == 11)

local total = 0
for i = 1, 3 do
    total = total + i
end

local x = 0
local y = 0
if x == 0 then
    goto left
end
goto right

::left::
x = x + 1
y = y + 10
if x < 3 then
    goto right
end
goto done

::right::
x = x + 2
y = y + 1
if y < 13 then
    goto left
end

::done::
assert(total == 6 and x == 4 and y == 21)
print("regress_182_numeric_for_before_irreducible_goto#1", total, x, y)

-- cycle=true 不终止；nil 与 0 分别走 first 与 second 入口。
assert(prefix_before_irreducible(nil, nil) == 11)
assert(prefix_before_irreducible(0, false) == 10)
-- unluac: expect-ast-count [[numeric-for]] [[1]]
-- unluac: expect-ast-count [[goto]] [[2]] [[@proto=1]]
-- unluac: expect-ast-count [[label]] [[2]] [[@proto=1]]
-- unluac: expect-ast-count [[while]] [[0]]
-- unluac: expect-ast-count [[repeat]] [[0]]
-- 初值在 print 之后声明，两个入口与回边共用该状态，不生成额外 phi 声明或转存。
-- unluac: expect-ast-count [[local-binding]] [[2]] [[@proto=1]]
-- unluac: expect-ast-count [[empty-local]] [[0]] [[@proto=1]]
-- unluac: expect-ast-count [[assign]] [[2]] [[@proto=1]]
-- 主函数的 x/y 沿不可规约区域原位更新，不拆成各条边的空 phi 变量。
-- unluac: expect-ast-count [[empty-local]] [[0]] [[@proto=0]]
-- 原闭包声明足以承接四次调用；callee 与结果准备不能变成跨调用或循环的状态。
-- unluac: expect-ast-count [[local-binding]] [[5]] [[@proto=0]]
-- unluac: expect-ast-count [[assign]] [[5]] [[@proto=0]]
