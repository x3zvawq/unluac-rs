-- regress_444_lua55_singleton_global_hir_owner: 单结果初始化由 HIR global 协议直接认领
-- unluac: expect-contains [[global singleton_target =]]
-- unluac: expect-count [[global singleton_target =]] [[1]]
-- unluac: expect-ast-count [[global-decl]] [[2]]
-- unluac: expect-ast-count [[function]] [[1]]
-- unluac: expect-ast-count [[error]] [[0]]

global<const> print, assert

local calls = 0
local function make_value()
    calls = calls + 1
    return 42
end

global singleton_target = make_value()
assert(singleton_target == 42 and calls == 1)
print("regress_444_lua55_singleton_global_hir_owner", singleton_target)
