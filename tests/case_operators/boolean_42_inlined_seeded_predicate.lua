-- 显式 Boolean 初始化的展开函数既作独立结果，也作观察调用的中间实参。
-- __index 轨迹保护逐次字段读取；三轮再编译保护共同返回槽，不能产生 repeat/break 包装。
-- unluac: expect-ast-count [[function]] [[2]]
-- unluac: expect-ast-count [[local-binding]] [[5]]
-- unluac: expect-ast-count [[repeat]] [[0]]
-- unluac: expect-ast-count [[local-decl]] [[1]] [[@proto=1]]
local function seeded(flags)
    local result = false
    if not flags.a and not flags.b then
        if flags.c and flags.d then result = true
        elseif flags.e then result = true
        elseif flags.f and flags.g then result = true end
    end
    return result
end

local reads = ""
local flags = setmetatable({}, {
    __index = function(_, key)
        reads = reads .. key
        return key == "e"
    end,
})
local result = seeded(flags)
assert(result and reads == "abce")
reads = ""
print("seeded-inline", seeded(flags), reads)
