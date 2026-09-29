-- unluac: expect-ast-count [[function]] [[0]]
-- unluac: expect-ast-count [[local-binding]] [[1]]
-- unluac: expect-ast-count [[error]] [[0]]
-- regress_309_ignore_debug_keeps_validation#1: ignore-debug 不能绕过损坏 debug 尾段的严格校验
local debug_validation_name = 7
assert(debug_validation_name == 7)
print("regress_309_ignore_debug_keeps_validation#1", debug_validation_name)
