-- 不可达源码仍可留下没有 SSA use 的 Move；预计算值根不能因此拒绝整个函数。
-- unluac: expect-not-contains [[unresolved]]
-- unluac: expect-not-contains [[unluac error]]
local function entry(flag, value)
    do return flag, value end
    local copied = value
    if flag then copied = flag end
    return copied
end

assert(select(2, entry(false, 23)) == 23)
assert(select(2, entry(true, "value")) == "value")
print("regress_490_unreachable_move_facts", "OK")
