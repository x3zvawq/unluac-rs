-- regress_72_loop_exit_generic_owner#1: loop-owned exit phi suppresses its generic candidate
-- unluac: expect-contains [[while r0_0 < 2 do]]
-- unluac: expect-contains [[return r0_0]]
-- unluac: expect-not-contains [[unresolved]]
-- unluac: expect-not-contains [[unluac error]]
-- 固定输入只执行正常出口；原 break 检查不可达，但仍须保留其原控制关系。
-- unluac: expect-ast-count [[local-binding]] [[1]] [[@proto=0]]
-- unluac: expect-ast-count [[while]] [[1]] [[@proto=0]]
-- unluac: expect-ast-count [[if]] [[1]] [[@proto=0]]
-- unluac: expect-ast-count [[break]] [[1]] [[@proto=0]]

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
