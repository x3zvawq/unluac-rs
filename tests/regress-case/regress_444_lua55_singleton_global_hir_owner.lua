-- regress_444_lua55_singleton_global_hir_owner: 单结果初始化由 HIR global 协议直接认领
-- unluac: expect-contains [[global singleton_target =]]

global<const> print

local function make_value()
    return 42
end

global singleton_target = make_value()
print("regress_444_lua55_singleton_global_hir_owner", singleton_target)
