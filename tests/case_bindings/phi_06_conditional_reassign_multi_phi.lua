-- regress_47_conditional_reassign_multi_phi#1: conditional reassign 不能拆开同一分支的多输出 phi
-- unluac: expect-not-contains [[unluac error]]

local function sample(cond)
    local a, b = "old-a", "old-b"
    if cond then
        cond = false
        a, b = "new-a", "new-b"
    end
    return a, b, cond
end

local true_a, true_b, true_cond = sample(true)
local false_a, false_b, false_cond = sample(false)
assert(true_a == "new-a" and true_b == "new-b" and true_cond == false)
assert(false_a == "old-a" and false_b == "old-b" and false_cond == false)
print("regress_47_conditional_reassign_multi_phi#1", true_a, true_b, true_cond, false_a, false_b, false_cond)
