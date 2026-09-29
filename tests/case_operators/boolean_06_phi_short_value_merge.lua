-- regress_234_nested_phi_short_value_merge#1: 短路值叶经中间 Phi 汇入外层 merge
-- unluac: expect-not-contains [[unluac error]]
-- unluac: expect-not-contains [[unresolved]]
-- unluac: expect-not-contains [[if p2_1 then]]
-- unluac: expect-not-contains [[local r1_0 = p1_1 or p1_0]]
-- unluac: expect-not-contains [[local r1_0 = p1_0 and]]
-- unluac: expect-not-contains [[return r1_0]]
-- unluac: expect-contains [[return p]]
-- unluac: expect-ast-count [[function]] [[4]]
-- unluac: expect-ast-count [[numeric-for]] [[8]]
-- unluac: expect-ast-max [[local-binding]] [[1]] [[@proto=1]]
-- unluac: expect-ast-max [[local-binding]] [[1]] [[@proto=2]]
-- unluac: expect-ast-max [[local-binding]] [[1]] [[@proto=3]]
-- unluac: expect-ast-max [[local-binding]] [[1]] [[@proto=4]]
-- 固定 pick、共享 fallback 与运行 oracle 的字面量上限，每轮不得复制 continuation。
-- unluac: expect-max-count [["maybe"]] [[9]]
-- 两次计数矩阵沿用原状态声明，后续 CALL 不留下逐轮增长的准备别名。
-- unluac: expect-ast-max [[local-binding]] [[21]] [[@proto=0]]
-- unluac: expect-max-count [[= assert]] [[0]]
-- unluac: expect-max-count [[= select]] [[0]]
local function pick(x, a, b, c)
    local out
    if x then
        out = a or x
    else
        out = (b and (c and "maybe" or "no")) or x
    end
    return out
end

local first = pick(true, true, false, true)
local second = pick(false, false, true, true)
local third = pick(false, false, true, false)
local fourth = pick(false, false, false, true)
assert(first == true)
assert(second == "maybe")
assert(third == "no")
assert(fourth == false)
print(first, second, third, fourth)

-- 位置而非同形短路表达式作为 oracle；覆盖 false/nil 与真值对象的返回身份。
local values = { false, true, 0, "", {} }
local combinations = 0
for xi = 1, 6 do
    for ai = 1, 6 do
        for bi = 1, 6 do
            for ci = 1, 6 do
                local expected
                if xi == 1 or xi == 6 then
                    if bi == 1 or bi == 6 then
                        expected = values[xi]
                    elseif ci == 1 or ci == 6 then
                        expected = "no"
                    else
                        expected = "maybe"
                    end
                elseif ai == 1 or ai == 6 then
                    expected = values[xi]
                else
                    expected = values[ai]
                end
                assert(pick(values[xi], values[ai], values[bi], values[ci]) == expected)
                combinations = combinations + 1
            end
        end
    end
end
assert(select("#", pick(nil, nil, nil, nil)) == 1)
assert(combinations == 1296)
print("phi_pick_matrix", combinations)

local function shared_fallback(x, a, b, c)
    local out
    if x then
        out = a and ((x == true and "yes") or (c and "maybe") or "no")
            or x
            or (b and ((x == true and "yes") or (c and "maybe") or "no"))
            or x
    else
        out = x
            or (b and ((x == true and "yes") or (c and "maybe") or "no"))
            or x
    end
    return out or "false"
end

assert(shared_fallback(true, true, false, true) == "yes")
assert(shared_fallback(false, false, true, true) == "maybe")
assert(shared_fallback(false, false, false, true) == "false")
combinations = 0
for xi = 1, 6 do
    for ai = 1, 6 do
        for bi = 1, 6 do
            for ci = 1, 6 do
                local expected
                if xi ~= 1 and xi ~= 6 then
                    if ai == 1 or ai == 6 then
                        expected = values[xi]
                    elseif xi == 2 then
                        expected = "yes"
                    elseif ci == 1 or ci == 6 then
                        expected = "no"
                    else
                        expected = "maybe"
                    end
                elseif bi == 1 or bi == 6 then
                    expected = "false"
                elseif ci == 1 or ci == 6 then
                    expected = "no"
                else
                    expected = "maybe"
                end
                assert(shared_fallback(values[xi], values[ai], values[bi], values[ci]) == expected)
                combinations = combinations + 1
            end
        end
    end
end
assert(combinations == 1296)
assert(select("#", shared_fallback(nil, nil, nil, nil)) == 1)

local repeated_calls = 0
local function same_call()
    repeated_calls = repeated_calls + 1
    return repeated_calls == 1
end

local function call_twice_on_truthy_path()
    local value
    if same_call() then
        value = same_call()
    else
        value = "not called"
    end
    return value
end

assert(call_twice_on_truthy_path() == false)
assert(repeated_calls == 2)
assert(call_twice_on_truthy_path() == "not called")
assert(repeated_calls == 3)
assert(select("#", call_twice_on_truthy_path()) == 1)
assert(repeated_calls == 4)
