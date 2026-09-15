-- regress_123_luau_dual_early_return_soft_merge#1: 两臂 early return 不丢失共同尾部的值 merge
-- unluac: expect-contains [[return]]
-- unluac: expect-not-contains [[unresolved]]
-- unluac: expect-not-contains [[unluac error]]
-- unluac: expect-ast-max [[if]] [[3]] [[@proto=1]]
local subject = function(a, b, c)
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

-- 经表调用保留被测 proto，不让优化编译器直接内联并消去输入分支。
local dispatch = { subject }
for _, a in ipairs({ false, true }) do
    for _, b in ipairs({ false, true }) do
        for _, c in ipairs({ false, true }) do
            local result = dispatch[1](a, b, c)
            assert(result == (a and 1 or 2))
            print("regress_123#1", a, b, c, result)
        end
    end
end
