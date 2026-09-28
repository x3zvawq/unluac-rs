-- regress_48_decision_value_truthiness#1: value context 不能使用 condition-only truthiness 简化
-- 原 LOADBOOL true 后仍有 TEST，不能按常量值域消掉这次显式检查。
-- unluac: expect-contains [[return p1_0 and true or false]]

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
