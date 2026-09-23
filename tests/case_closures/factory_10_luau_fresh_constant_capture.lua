-- 原 NEWCLOSURE 的局部 capture 不能因重新编译常量传播而变成共享 DUPCLOSURE。
-- unluac: expect-not-contains [[unresolved]]
-- unluac: expect-not-contains [[unluac error]]
-- O2 的发布表展开体与外层 CALL 一起恢复，不留下根交接或 callee 赋值。
-- unluac: expect-ast-count [[assign]] [[0]] [[@proto=0]]
-- unluac: expect-contains [[print("capture-boundaries",]]
-- 前一组的展开表写入不能把后续 selector 声明退化为 callee 交接。
-- unluac: expect-ast-count [[do-block]] [[4]] [[@proto=0]] [[@debug=stripped]]
-- unluac: expect-contains [[local missing = scalar_factory()]] [[@debug=retained]]
-- unluac: expect-contains [[local falsy = scalar_factory(false)]] [[@debug=retained]]
-- unluac: expect-contains [[local truthy = scalar_factory(true)]] [[@debug=retained]]
local function opaque(value) return value end

local function nan_factory(...)
    local nan = opaque(0/0)
    return function() return nan end
end

local function scalar_factory(...)
    local value = opaque(7)
    return function() return value end
end

-- 不同 phi 值与 ByReference capture 不属于同值 ByValue 初始化事务。
local function choice_factory(...)
    local value = (...) and 7 or 9
    return function() return value end
end
local function mutable_factory(...)
    local value = opaque(7)
    local getter = function() return value end
    value = 9
    return getter
end

do
    local first = nan_factory()
    local second = nan_factory()
    local first_value = first()
    local second_value = second()
    assert(first ~= second, "fresh NaN captures were shared across activations")
    assert(first_value ~= first_value)
    assert(second_value ~= second_value)
    print("fresh-nan", first == second, first_value ~= first_value, second_value ~= second_value)
end

do
    local first = scalar_factory()
    local second = scalar_factory()
    local first_value = first()
    local second_value = second()
    assert(first ~= second, "fresh scalar captures were shared across activations")
    assert(first_value == 7)
    assert(second_value == 7)
    print("fresh-scalar", first == second, first_value, second_value)
end

-- 首 vararg 复制只能暂借原 closure 结果槽；原 vararg 区必须继续强持有参数。
local weak = setmetatable({}, { __mode = "v" })
local function resource()
    local value = {}
    weak[1] = value
    return value
end
local function churn()
    for i = 1, 20000 do
        local garbage = { i, i + 1, i + 2, i + 3 }
    end
end
local function capture_with_argument(...)
    local value = opaque(7)
    local closure = function() return value end
    churn()
    assert(weak[1] ~= nil, "original vararg lost its strong root")
    return closure
end
do
    local first = capture_with_argument(resource())
    local second = capture_with_argument(resource())
    local first_value = first()
    local second_value = second()
    assert(first ~= second)
    assert(first_value == 7)
    assert(second_value == 7)
    print("fresh-vararg-root", first == second, first_value, second_value)
end

-- 两条分支都必须保持初始值和 Fresh 身份，包括缺省、false 与 truthy 首参数。
do
    local missing = scalar_factory()
    local falsy = scalar_factory(false)
    local truthy = scalar_factory(true)
    local missing_value = missing()
    local falsy_value = falsy()
    local truthy_value = truthy()
    assert(missing ~= falsy)
    assert(falsy ~= truthy)
    assert(missing_value == 7)
    assert(falsy_value == 7)
    assert(truthy_value == 7)
    print("fresh-selectors", missing_value, falsy_value, truthy_value)
end

do
    local first = choice_factory(false)
    local second = choice_factory(true)
    local mutable = mutable_factory()
    local first_value = first()
    local second_value = second()
    local mutable_value = mutable()
    assert(first_value == 9)
    assert(second_value == 7)
    assert(mutable_value == 9)
    print("capture-boundaries", first_value, second_value, mutable_value)
end
