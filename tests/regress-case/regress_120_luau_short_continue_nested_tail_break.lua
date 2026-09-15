-- regress_120_luau_short_continue_nested_tail_break#1: 短路 continue 后的 nested repeat 与 tail break 保持独立 owner
-- unluac: expect-contains [[repeat]]
-- unluac: expect-contains [[continue]]
-- unluac: expect-contains [[break]]
-- unluac: expect-not-contains [[goto ]]
-- unluac: expect-not-contains [[::L]]
-- unluac: expect-not-contains [[unresolved]]
-- unluac: expect-not-contains [[unluac error]]
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
-- a=false 的非终止分支没有等价的有限退出，本观察不声称覆盖那些路径或全部 continue owner。
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
