-- 原调用帧需要的声明仍保留初始化值；entry-nil 只说明旧槽值，不能把 false 改成 nil。
-- 循环后的同级声明也保留原值，不因没有读取而变成空初始化。
-- unluac: expect-count [[ = false]] [[3]]
-- unluac: expect-not-contains [[ = nil]]
-- unluac: expect-ast-count [[local-decl]] [[1]] [[@proto=0]]
-- unluac: expect-ast-count [[local-decl]] [[1]] [[@proto=1]]

local discarded = false

local function after_while(flag)
    while flag do
        flag = false
    end
    local discarded_after_loop = false
    print("after-loop")
    return flag
end

local function run()
    return "ok"
end

assert(after_while(true) == false)
assert(after_while(false) == false)
assert(run() == "ok")
print("regress_345_dead_temp_entry_nil", run())
