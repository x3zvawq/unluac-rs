-- 循环尾的 continue 可恢复为条件更新；原比较、非选中值及 while 归属不能丢失。
-- unluac: expect-not-contains [[if true then]]
-- unluac: expect-count [[1 < 2]] [[1]]
-- unluac: expect-count [[2 < 1]] [[1]]
-- unluac: expect-count [[99]] [[3]]
-- unluac: expect-ast-count [[function]] [[2]]
-- unluac: expect-ast-count [[while]] [[2]]
-- unluac: expect-ast-count [[while]] [[1]] [[@proto=1]]
-- unluac: expect-ast-count [[while]] [[1]] [[@proto=2]]
-- unluac: expect-ast-count [[local-decl]] [[1]] [[@proto=1]]
-- unluac: expect-ast-count [[local-decl]] [[1]] [[@proto=2]]
-- unluac: expect-ast-count [[empty-local]] [[0]]
-- unluac: expect-not-contains [[goto ]]
-- unluac: expect-not-contains [[unresolved]]

local function run()
    local count = 0
    while count < 2 do
        count += 1
        local chosen = 1 < 2
        if chosen then
            continue
        else
            count = 99
        end
    end
    return count
end

assert(run() == 2)

-- 保留真实比较指令，同时执行原来的更新臂；不能只凭恒真样例的运行结果放行。
local function update()
    local count = 0
    while count < 2 do
        count += 1
        local chosen = 2 < 1
        if chosen then
            continue
        else
            count = 99
        end
    end
    return count
end

assert(update() == 99)
