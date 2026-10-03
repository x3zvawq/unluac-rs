-- regress_114_luau_repeat_shared_nested_loop_tail#1: repeat 分支共享嵌套 for tail
-- unluac: expect-contains [[repeat]]
-- unluac: expect-contains [[for ]]
-- unluac: expect-contains [[p1_0 or p1_2]]
-- unluac: expect-not-contains [[goto ]]
-- unluac: expect-not-contains [[::L]]
-- unluac: expect-not-contains [[unresolved]]
-- unluac: expect-not-contains [[unluac error]]
-- unluac: expect-ast-max [[local-binding]] [[10]] [[@proto=1]]
local function run(a, b, c, xs)
    local x = 0
    repeat
        if a then
            if xs[x] then break end
            while not b do
                for k, v in xs do
                    break
                end
                for k, v in xs do
                    x = x + 1
                end
                for k, v in xs do
                    x = x + 1
                    x = x + 1
                end
            end
            print(x)
        else
            if a then continue end
            repeat
                if a or c then
                    print(x)
                    print(x)
                else
                    x = x + 1
                    x = x + 1
                    x = x + 1
                end
            until b
        end
        for i = 1, 3 do
            x = x + 1
            repeat
                for k, v in xs do
                    x = x + 1
                    break
                end
                repeat
                    x = x + 1
                    x = x + 1
                until xs[x]
                break
            until not b
            for i = 1, 3 do
                while b do
                    x = x + 1
                end
            end
        end
        continue
    until c
    return x
end

print(
    "regress_114_luau_repeat_shared_nested_loop_tail#1",
    run(true, true, true, { [0] = true })
)

-- 分别进入共享尾部的两个前驱；索引观察器在原无界 while 前退出，核对迭代和累加顺序。
for mode = 1, 2 do
    local reads = {}
    local xs = setmetatable({ [99] = true }, {
        __index = function(_, key)
            reads[#reads + 1] = key
            if key == 0 then return false end
            error("shared-tail:" .. key, 0)
        end,
    })
    local ok, message = pcall(run, mode == 1, true, true, xs)
    assert(not ok and message == "shared-tail:4", message)
    assert(table.concat(reads, ",") == (mode == 1 and "0,4" or "4"))
    print("shared-tail-path", mode, table.concat(reads, ","))
end
