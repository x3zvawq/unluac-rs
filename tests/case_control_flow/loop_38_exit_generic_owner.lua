-- regress_72_loop_exit_generic_owner#1: loop-owned exit phi suppresses its generic candidate
-- 固定输入只执行正常出口；原 break 检查不可达，但仍须保留其原控制关系。

local result = 0
while result < 2 do
    result = result + 1
    if result > 3 then
        break
    end
end
assert(result == 2)
print("regress_72#1", result)
return result
