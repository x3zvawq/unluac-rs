-- regress_83_nested_break_exit_pad#1: nested branch chains belong to one break exit pad
-- unluac: expect-contains [[while ]]
-- unluac: expect-contains [[break]]
-- unluac: expect-not-contains [[goto ]]
-- unluac: expect-not-contains [[::L]]
-- unluac: expect-not-contains [[unluac error]]
-- unluac: expect-not-contains [[(function()]]
-- 原检查保留在条件中，不生成丢弃布尔结果的局部变量或短作用域。
-- unluac: expect-ast-count [[local-decl]] [[1]] [[@proto=1]]
-- unluac: expect-ast-count [[do-block]] [[0]] [[@proto=1]]
-- unluac: expect-ast-count [[if]] [[3]] [[@proto=1]]
-- unluac: expect-ast-count [[while]] [[1]] [[@proto=1]]
local function run(a, b, xs)
    local rounds = 0
    while not b do
        rounds = rounds + 1
        -- continue 路径原本无限循环；有限入口计数让它也能被运行时观察。
        if rounds == 3 then return rounds end
        if a then
            if xs[1] then
                break
            end
        else
            continue
        end
        if a and b then
            break
        end
        break
    end
    print("regress_83_nested_break_exit_pad#1 done")
    return rounds
end

local reads = 0
local value = true
local xs = setmetatable({}, { __index = function(_, key)
    assert(key == 1)
    reads = reads + 1
    return value
end })
assert(run(true, false, xs) == 1 and reads == 1)
value = false
assert(run(true, false, xs) == 1 and reads == 2)
assert(run(false, false, xs) == 3 and reads == 2)
assert(run(true, true, xs) == 0 and reads == 2)
print("nested-break-paths", reads)
