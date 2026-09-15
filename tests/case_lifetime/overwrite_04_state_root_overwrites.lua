-- carried 身份的清根终点跨越无值读取的分支，不能变成独立死 temp。
-- unluac: expect-not-contains [[unluac error]]
-- unluac: expect-not-contains [[unresolved]]
-- unluac: expect-ast-count [[repeat]] [[1]]
local weak = setmetatable({}, { __mode = "v" })

local function run(swap, clear_with_nil)
    local left = { marker = 11 }
    local right = { marker = 22 }
    local holder = {}
    local round = 0
    repeat
        if swap then
            left, right = right, left
        else
            left, right = left, right
        end
        holder.value = right
        round = round + 1
    until round == 3
    assert(left.marker == (swap and 22 or 11))
    local function deliver()
        weak[1] = holder.value
        holder.value = nil
    end
    deliver()
    collectgarbage("collect")
    assert(weak[1] == right)
    assert(right.marker == (swap and 11 or 22))
    if clear_with_nil then
        right = nil
    else
        right = false
    end
    collectgarbage("collect")
    collectgarbage("collect")
    assert(weak[1] == nil, "carried root survived its scalar overwrite")
end

run(true, true)
run(true, false)
run(false, true)
run(false, false)

-- 自复制分量只有在目标唯一、所有 RHS 无观察时才能删除。
local x, y = 5, 6
x, x, y = x, 9, y
local before = x
local function mutate()
    x = 20
    return 30
end
x, y = x, mutate()
assert(x == before and y == 30)
print("parallel snapshot", x, y)
print("regress_474_loop_state_root_overwrites", "OK")
