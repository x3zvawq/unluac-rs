-- regress_345_dead_temp_entry_nil: 已证明 entry-nil 的死写可删除；原帧需要的占位保留为 nil。
-- 关闭 structured loop 后的 root sibling 同样不得留下无读 false 值。
-- unluac: expect-not-contains [[local r0_0 = false]]
-- unluac: expect-not-contains [[local r1_0 = false]]
-- unluac: expect-contains [[local r0_0 = nil]]
-- unluac: expect-ast-count [[local-decl]] [[1]] [[@proto=0]]

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
