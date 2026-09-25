-- 双入口岛的末尾只保留正向回跳；退出 RETURN 不在重编译时反复交换极性。
-- 两个 child 的 proto 编号在 PUC/JIT 间不同，按整个模块固定相同的结构。
-- unluac: expect-ast-count [[if]] [[2]]
-- unluac: expect-ast-count [[local-binding]] [[9]]
-- unluac: expect-not-contains [[if not (]]
local function run(entry, flag, limit)
    local value = nil
    local count = 0
    if entry then goto joined end
    ::fill::
    value = nil
    ::joined::
    if flag then value = true else value = false end
    count = count + 1
    if count < limit.stop then goto fill end
    return count
end

local checks = 0
local limit = setmetatable({}, {__index = function()
    checks = checks + 1
    return 3
end})
for _, entry in ipairs({false, true}) do
    for _, flag in ipairs({false, true}) do
        checks = 0
        assert(run(entry, flag, limit) == 3)
        assert(checks == 3, "each original comparison input must be read exactly once")
    end
end
print("island-return-goto-polarity", "OK")
