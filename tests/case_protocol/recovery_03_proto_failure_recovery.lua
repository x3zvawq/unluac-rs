-- regress_325_proto_failure_recovery: 测试框架会把根 HIR 替换为失败占位，
-- 验证 strict 拒绝失败 proto，permissive 保留诊断和直接子 proto。
local function first_child(value)
    return value + 1
end

local function second_child(value)
    return value * 2
end

print("regress_325_proto_failure_recovery", first_child(2), second_child(3))
