-- 未读结果仍占原 CALL 的第二个接收槽及后继 assert 前缀，不按 use count 单独删尾槽。

local function pair()
    return 17, 19
end

local keep, dead = pair()
assert(keep == 17)
