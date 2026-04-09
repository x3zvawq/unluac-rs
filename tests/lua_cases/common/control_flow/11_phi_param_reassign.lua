-- phi_param_reassign: 当函数参数在分支中被条件改写时, merge 点需要正确
-- 的 phi 合流。回归测试确保参数寄存器的空 reaching-defs 不会导致 phi 被
-- 静默拒绝, 从而引发反编译输出丢失原始参数值。

local function conditional_inc(x)
    if x > 0 then
        x = x + 1
    end
    return x
end

print(conditional_inc(3), conditional_inc(-1))
