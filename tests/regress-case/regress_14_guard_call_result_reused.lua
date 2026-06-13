-- regress_14_guard_call_result_reused#1: guard 链末尾 call 的返回值在 then 主逻辑里仍被读取时，
-- 不能把 call inline 进 and 条件而丢失赋值。
-- unluac: expect-not-contains [[unluac error]]
-- unluac: expect-not-contains [[and p2_1 and]]
-- unluac: expect-contains [[if p2_1 then]]
-- unluac: expect-contains [[missing_record]]
local function fetch_record(key)
    if key == 0 then
        return nil
    end
    return { key = key, entries = { 10, 20 } }
end

local function run(key, target)
    if not key then
        return "missing_key"
    end
    if not target then
        return "missing_target"
    end
    local record = fetch_record(key)
    if not record then
        return "missing_record"
    end
    local count = #record.entries
    for i = 1, count do
        if record.entries[i] == target then
            return "hit:" .. i
        end
    end
    return "miss"
end

return run(1, 10)
