-- regress_186_truthy_ternary_hir_owner#1: truthy ternary 的臂交换必须在 HIR 完成
-- unluac: expect-not-contains [[unluac error]]
-- unluac: expect-not-contains [[unresolved]]

local function choose(lhs, rhs)
    local different = lhs ~= rhs
    return different and function()
        return "different"
    end or function()
        return "same"
    end
end

print(
    "regress_186_truthy_ternary_hir_owner#1",
    choose("left", "right")(),
    choose("same", "same")()
)
