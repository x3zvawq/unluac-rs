-- 显式入口 nil 和两臂 Boolean 写共享原槽；循环 Phi 不应另起声明或让 nil 单独成块。
-- LuaJIT 的子函数编号不同；两份函数声明、reader 的一个值和 check 的四个 local 共七个。
-- unluac: expect-ast-count [[local-binding]] [[7]]
-- unluac: expect-ast-count [[while]] [[1]]
-- unluac: expect-max-count [[local r]] [[3]]
-- unluac: expect-not-contains [[ = coroutine.yield]]
local function reader(flag)
    local value = nil
    if flag then value = true else value = false end
    while true do
        coroutine.yield(value)
    end
end

local function check(flag)
    local co = coroutine.create(reader)
    for round = 1, 3 do
        local ok, value = coroutine.resume(co, flag)
        assert(ok and value == not not flag)
        assert(coroutine.status(co) == "suspended")
    end
end
check(false)
check(true)
check(nil)
check(0)
check("")
print("boolean_coroutine_phi", "OK")
