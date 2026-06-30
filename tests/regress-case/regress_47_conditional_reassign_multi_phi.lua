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

print("regress_47_conditional_reassign_multi_phi#1", sample(true), sample(false))
