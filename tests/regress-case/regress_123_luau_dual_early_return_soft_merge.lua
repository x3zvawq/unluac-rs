-- regress_123_luau_dual_early_return_soft_merge#1: 两臂 early return 不丢失共同尾部的值 merge
-- unluac: expect-contains [[return]]
-- unluac: expect-not-contains [[unresolved]]
-- unluac: expect-not-contains [[unluac error]]
return function(a, b, c)
    local x
    if a then
        x = 1
        if b then
            return x
        end
    else
        x = 2
        if c then
            return x
        end
    end
    return x
end
