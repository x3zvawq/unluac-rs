-- 显式入口 nil 和两臂 Boolean 写共享原槽；循环 Phi 不应另起声明或让 nil 单独成块。
-- LuaJIT 的子函数编号不同；两份函数声明、reader 的一个值和 check 的四个 local 共七个。
-- unluac: expect-ast-count [[local-binding]] [[7]]
-- unluac: expect-ast-count [[while]] [[1]]
-- unluac: expect-ast-count [[numeric-for]] [[1]]
-- unluac: expect-ast-count [[function]] [[2]]
-- unluac: expect-ast-count [[empty-local]] [[0]]
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
        -- 后续恢复传入 false；yield 返回值不能替代首次建立的 Boolean 状态。
        local ok, value = coroutine.resume(co, round == 1 and flag)
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
