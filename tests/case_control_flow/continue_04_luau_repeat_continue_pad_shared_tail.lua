-- regress_117_luau_repeat_continue_pad_shared_tail#1: repeat continue pad 不消费共享 tail 与 condition
-- unluac: expect-contains [[continue]]
-- O2 内联并展开循环后仍有六次 ADD；运行输出为 6 不代表可以删除这些运算。
-- unluac: expect-contains [[0 + 1 + 1 + 1 + 1 + 1 + 1]]
-- 重复的 a 检查决定原 continue 边，不能按外层路径假设删除。
-- unluac: expect-contains [[                if p1_0 then]]
-- 循环 limit 与后继 Boolean 写承接旧根覆盖，回编译不应另外增生清空语句。
-- unluac: expect-max-count [[ = nil]] [[0]]
-- unluac: expect-not-contains [[goto ]]
-- unluac: expect-not-contains [[::L]]
-- unluac: expect-not-contains [[unresolved]]
-- unluac: expect-not-contains [[unluac error]]
-- unluac: expect-ast-count [[numeric-for]] [[1]] [[@proto=1]]
-- unluac: expect-ast-count [[repeat]] [[1]] [[@proto=1]]
-- unluac: expect-ast-count [[if]] [[3]] [[@proto=1]]
-- unluac: expect-ast-count [[continue]] [[1]] [[@proto=1]]
-- unluac: expect-ast-count [[empty-local]] [[0]] [[@proto=1]]
-- 索引回调的算术及比较参数直接沿原帧求值，不制造独立准备声明。
-- unluac: expect-ast-count [[local-decl]] [[0]] [[@proto=2]]
local function run(a, b, xs)
    local x = 0
    for i = 1, 3 do
        x = x + 1
        repeat
            if a then
                if xs[x] then break end
                if a then continue else x = x + 1 end
            end
            x = x + 1
        until b
    end
    return x
end

print("regress_117_luau_repeat_continue_pad_shared_tail#1", run(false, true, {}))
print("regress_117_luau_repeat_continue_pad_shared_tail#2", run(true, true, {}))
print("regress_117_luau_repeat_continue_pad_shared_tail#3", run(true, true, { [1] = true }))

-- b=false 时通过可观察索引在每轮第三次读取退出；前两次 continue 必须
-- 跳过 x 的正文尾部写入，并重新执行同一轮的 until。a=false,b=false
-- 本来就没有退出路径，不把它当作有限运行样例。
for _, b in ipairs({true, false}) do
    for _, hit in ipairs({true, false}) do
        local reads = 0
        local period = (b or hit) and 1 or 3
        local xs = setmetatable({}, {__index = function(_, key)
            reads = reads + 1
            assert(reads <= 9)
            assert(key == math.floor((reads - 1) / period) + 1)
            return hit or (not b and reads % 3 == 0)
        end})
        assert(run(true, b, xs) == 3)
        assert(reads == 3 * period)
        print("continue shared tail", b, hit, reads)
    end
end
local no_read = setmetatable({}, {__index = function()
    error("a=false must skip the indexed guard")
end})
assert(run(false, true, no_read) == 6)
