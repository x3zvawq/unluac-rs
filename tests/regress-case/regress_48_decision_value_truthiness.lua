-- regress_48_decision_value_truthiness#1: value context 不能使用 condition-only truthiness 简化
-- unluac: expect-contains [[return p1_0 and true or false]]

local function normalize(value)
    return (value and true) or false
end

print("regress_48_decision_value_truthiness#1", normalize(nil), normalize(false), normalize(7))
