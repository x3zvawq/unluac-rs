-- regress_162_table_checkpoint_new_pending_rollback#1: 候选内新建并搬移的整数字段在失败回滚时不得越过字段边界
-- unluac: expect-contains [[[2] = "second"]]
-- unluac: expect-contains [[[1] =]]
-- unluac: expect-not-contains [[unluac error]]
local calls = 0

local function produce()
    calls = calls + 1
    return "first"
end

local t = {}
local value = produce()
t[2] = "second"
t[1] = value

print("regress_162_table_checkpoint_new_pending_rollback#1", calls, value, #t, t[1], t[2])
