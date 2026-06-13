-- regress_15_branch_preserved_nil_seed#1: 条件赋值后 `if not v then return` 时，
-- 未走 then 臂的寄存器在 Lua 里就是 nil，不能留下 entry-reg unresolved。
-- unluac: expect-not-contains [[unluac error]]
-- unluac: expect-not-contains [[entry-reg]]
local function fetch_record(key)
    if key == 0 then
        return nil
    end
    return { id = key, scale = 1024 }
end

local function run(key, amount)
    local record
    if key and key > 0 then
        record = fetch_record(key)
    end
    if not record then
        return "missing"
    end
    return amount * record.scale / 1024
end

return run(1, 100)
