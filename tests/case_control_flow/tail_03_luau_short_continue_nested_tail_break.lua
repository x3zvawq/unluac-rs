-- regress_120_luau_short_continue_nested_tail_break#1: 短路 continue 后的 nested repeat 与 tail break 保持独立 owner
-- unluac: expect-contains [[repeat]]
-- unluac: expect-contains [[continue]]
-- unluac: expect-contains [[break]]
-- unluac: expect-not-contains [[goto ]]
-- unluac: expect-not-contains [[::L]]
-- unluac: expect-not-contains [[unresolved]]
-- unluac: expect-not-contains [[unluac error]]
-- unluac: expect-ast-count [[numeric-for]] [[1]] [[@proto=1]]
-- unluac: expect-ast-count [[while]] [[1]] [[@proto=1]]
-- unluac: expect-ast-count [[generic-for]] [[2]] [[@proto=1]]
-- unluac: expect-ast-count [[repeat]] [[2]] [[@proto=1]]
-- unluac: expect-ast-count [[local-binding]] [[6]] [[@proto=1]]
-- 有界观察中的多入口和兄弟循环同样只保留一个累积状态。
-- unluac: expect-ast-count [[local-binding]] [[6]] [[@proto=4]]
-- unluac: expect-ast-count [[local-binding]] [[6]] [[@proto=5]]
local function tested(a, b, c, xs)
    local x = 0
    for i = 1, 3 do
        x = x + 1
        repeat
            if a then
                if xs[x] then break end
                if a then continue else x = x + 1 end
            else
                while b do
                    x = x + 1
                    x = x + 1
                end
                for k, v in xs do
                    x = x + 1
                end
                if a or c then continue end
            end
            repeat
                for k, v in xs do
                    x = x + 1
                    x = x + 1
                end
            until not b
            if a and b then break end
        until a
    end
    return x
end

-- pcall 保留优化编译时的目标 proto；__index 观察 x 的跨轮状态及查表次数、顺序。
-- a=false 的分支在下方由迭代器有界中断；b=true 的纯算术无限循环不声称运行覆盖。
local indexes, take_break = {}, false
local xs = setmetatable({}, {
    __index = function(_, key)
        indexes[#indexes + 1] = key
        return take_break
    end,
})
for _, mode in ipairs({ false, true }) do
    indexes, take_break = {}, mode
    local ok, result = pcall(tested, true, false, false, xs)
    assert(ok and result == 3 and table.concat(indexes, ",") == "1,2,3")
    print("regress_120#1", mode, result, table.concat(indexes, ","))
end

indexes, take_break = {}, 0
local ok, result = pcall(tested, 0, nil, "", xs)
assert(ok and result == 3 and table.concat(indexes, ",") == "1,2,3")

local calls = 0
local function iterator(_, control)
    calls = calls + 1
    assert(calls <= 6, "observed repeat backedge")
    if control == nil then
        return 1
    end
end
assert(not pcall(tested, false, false, true, iterator))
assert(calls == 7)
calls = 0
assert(not pcall(tested, false, false, false, iterator))
assert(calls == 7)

-- 有界版本实际观察两个入口汇入 repeat 后的状态，覆盖兄弟遍历和嵌套回边。
local function carried(choose, values)
    local x = 0
    for i = 1, 2 do
        repeat
            if choose then
                x = x + 1
            else
                for _, value in values do
                    x = x + value
                end
            end
            repeat
                for _, value in values do
                    x = x + value
                end
            until x >= 4
        until x >= 7
    end
    return x
end
ok, result = pcall(carried, true, {1, 2})
assert(ok and result == 12)
ok, result = pcall(carried, false, {1, 2})
assert(ok and result == 18)
print("regress_120_carried", result)

-- 外层选择独立后，内层 a=true 的短路 continue 必须直接到 until，不能执行后续 repeat。
local function independent(outer, a, b, c, values)
    local x = 0
    for i = 1, 3 do
        x = x + 1
        repeat
            if outer then
                if values[x] then break end
                if a then continue else x = x + 1 end
            else
                while b do
                    x = x + 1
                    x = x + 1
                end
                for _, value in values do
                    x = x + 1
                end
                if a or c then continue end
            end
            repeat
                for _, value in values do
                    x = x + 1
                    x = x + 1
                end
            until not b
            if a and b then break end
        until a
    end
    return x
end
ok, result = pcall(independent, false, true, false, false, {1})
assert(ok and result == 6)
print("regress_120_independent", result)
