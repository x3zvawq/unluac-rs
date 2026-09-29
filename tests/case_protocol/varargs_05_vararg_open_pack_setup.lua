-- unluac: expect-ast-count [[function]] [[2]]
-- unluac: expect-ast-max [[local-binding]] [[5]] [[@proto=0]]
-- unluac: expect-ast-max [[local-binding]] [[6]]
-- 原 abs 快照保留；开放包之后的 callee COPY 不另建源码绑定。
-- unluac: expect-ast-count [[local-binding]] [[1]] [[@dialect=luau]] [[@proto=1]]
-- unluac: expect-ast-count [[local-binding]] [[0]] [[@dialect=luau]] [[@proto=2]]
-- unluac: expect-ast-count [[error]] [[0]]
-- regress_191_vararg_open_pack_setup#1: VarArg open tail 可跨 callee setup
-- unluac: expect-contains [[...]]
-- unluac: expect-not-contains [[unresolved]]
-- unluac: expect-not-contains [[unluac error]]

local function direct(...)
    local abs = math.abs
    return abs(...)
end

local abs = math.abs
local function captured(...)
    return abs(...)
end

local direct_result, captured_result = direct(-5), captured(-6)
assert(direct_result == 5 and captured_result == 6)
print("regress_191_vararg_open_pack_setup#1", direct_result, captured_result)

-- 空包和 nil 首参必须保留 builtin 的失败行为，额外参数不能替换原首参。
assert(not pcall(direct))
assert(not pcall(direct, nil))
assert(direct(-9, nil, "ignored") == 9)
assert(captured(-7, nil) == 7)
