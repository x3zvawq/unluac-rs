-- regress_465_scope_end_copy_root_coverage: a dead copy and its source share a frame-end root.
-- Removing the duplicate must retain the source snapshot at its original evaluation point.
local held = {}
local weak = setmetatable({ value = held }, { __mode = "v" })

local function retain(callback)
    local source = held
    held = nil
    local duplicate = source
    -- 子块内联先改变 HIR；随后删除 dead copy 时必须查询当前 home 写入快照。
    if callback then
        local n = 1 + 1
        assert(n == 2)
    end
    callback()
end

retain(function()
    collectgarbage("collect")
    collectgarbage("collect")
    assert(weak.value ~= nil, "scope-end owner disappeared with its dead copy")
end)
collectgarbage("collect")
collectgarbage("collect")
assert(weak.value == nil, "scope-end owner escaped its function lifetime")
print("regress_465_scope_end_copy_root_coverage", "OK")
