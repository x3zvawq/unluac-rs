-- regress_48_decision_value_truthiness#1: value context 不能使用 condition-only truthiness 简化
-- 原 LOADBOOL true 后仍有 TEST，不能按常量值域消掉这次显式检查。
-- unluac: expect-contains [[return p1_0 and true or false]]
-- unluac: expect-ast-count [[function]] [[3]]
-- unluac: expect-ast-count [[if]] [[0]] [[@proto=1]]
-- unluac: expect-ast-count [[if]] [[0]] [[@proto=2]]
-- unluac: expect-ast-count [[numeric-for]] [[3]]
-- unluac: expect-ast-max [[local-binding]] [[14]]

local function normalize(value)
    return (value and true) or false
end

print("regress_48_decision_value_truthiness#1", normalize(nil), normalize(false), normalize(7))
assert(normalize(nil) == false and normalize(false) == false)
assert(normalize(0) == true and normalize(7) == true and normalize("") == true)

-- 共享 continuation 只求值一次；CurrentValue 仍区分 nil、false 和 Lua 中为真的 0。
local function traced(a, b, c)
    local trace = ""
    local function hit(label, value)
        trace = trace .. label
        return value
    end
    local value = (hit("a", a) and hit("b", b) or hit("c", c) and hit("d", true)) and hit("t", 0)
    return value, trace
end
local value, trace = traced(false, true, nil)
assert(value == nil and trace == "ac")
value, trace = traced(false, true, false)
assert(value == false and trace == "ac")
value, trace = traced(true, 0, false)
assert(value == 0 and trace == "abt")
value, trace = traced(true, false, "fallback")
assert(value == 0 and trace == "abcdt")
print("regress_48_decision_value_truthiness#2", "OK")

-- 用位置及分支轨迹作独立 oracle，覆盖每个短路入口的 nil/false/真值。
local values = { false, true, 0, "", {} }
local combinations = 0
for ai = 1, 6 do
    for bi = 1, 6 do
        for ci = 1, 6 do
            local expected, expected_trace
            if ai ~= 1 and ai ~= 6 then
                if bi ~= 1 and bi ~= 6 then
                    expected, expected_trace = 0, "abt"
                elseif ci ~= 1 and ci ~= 6 then
                    expected, expected_trace = 0, "abcdt"
                else
                    expected, expected_trace = values[ci], "abc"
                end
            elseif ci ~= 1 and ci ~= 6 then
                expected, expected_trace = 0, "acdt"
            else
                expected, expected_trace = values[ci], "ac"
            end
            value, trace = traced(values[ai], values[bi], values[ci])
            assert(value == expected and trace == expected_trace)
            combinations = combinations + 1
        end
    end
end
assert(combinations == 216)
assert(select("#", traced(nil, nil, nil)) == 2)
assert(select("#", normalize(nil)) == 1)
assert(normalize({}) == true)
