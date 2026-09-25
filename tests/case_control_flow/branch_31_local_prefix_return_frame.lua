-- 已有 local 后的两条返回路径共用 scratch，不能留下只为 RETURN 准备的临时声明。
-- unluac: expect-ast-count [[if]] [[0]] [[@proto=1]]
-- 剥离 debug 后允许 selected 一并内联；保留 debug 时仍须保留它的源码身份。
-- unluac: expect-ast-max [[local-binding]] [[1]] [[@proto=1]]
-- unluac: expect-ast-count [[local-binding]] [[1]] [[@proto=1]] [[@debug=retained]]

local function choose(value, enabled)
    local selected = enabled and value or false
    return not selected and "fallback" or selected
end

local token = {}
assert(choose(nil, true) == "fallback")
assert(choose(false, true) == "fallback")
assert(choose(token, false) == "fallback")
assert(choose(token, true) == token)
assert(choose(0, true) == 0)
assert(choose("", true) == "")
print("branch_local_prefix_return_frame")
