-- common_15: 组合覆盖内外层 break、repeat 尾条件事件和外层回边状态。
-- unluac: expect-ast-min [[repeat]] [[2]] [[@dialect=lua5.4]] [[@proto=1]]
-- unluac: expect-ast-min [[while]] [[1]] [[@dialect=lua5.4]] [[@proto=1]]
local function observe(early, inner, stop)
    local trace = {}
    local i, total = 0, 0
    local function tail(tag, value)
        trace[#trace + 1] = tag
        return value
    end
    while i < 3 do
        i = i + 1
        local j = 0
        repeat
            j = j + 1
            total = total + 1
            if early and i == 2 then
                break
            end
            local k = 0
            repeat
                k = k + 1
                total = total + 10
                if inner then
                    break
                end
            until tail("inner", k == 2)
            if stop and j == 1 then
                break
            end
        until tail("outer", j == 2)
        total = total + 100
    end
    return total, table.concat(trace, ",")
end

-- 独立的有限展开 oracle：条件事件应仅发生在未执行 break 的路径。
local function expected(early, inner, stop)
    local trace, total = {}, 0
    for i = 1, 3 do
        if early and i == 2 then
            total = total + 1
        else
            local rounds = stop and 1 or 2
            for j = 1, rounds do
                total = total + 1
                if inner then
                    total = total + 10
                else
                    total = total + 20
                    trace[#trace + 1] = "inner"
                    trace[#trace + 1] = "inner"
                end
                if not stop then
                    trace[#trace + 1] = "outer"
                end
            end
        end
        total = total + 100
    end
    return total, table.concat(trace, ",")
end

for mask = 0, 7 do
    local early = mask % 2 == 1
    local inner = math.floor(mask / 2) % 2 == 1
    local stop = mask >= 4
    local value, trace = observe(early, inner, stop)
    local want_value, want_trace = expected(early, inner, stop)
    assert(value == want_value)
    assert(trace == want_trace)
    print("common_15#1", mask, value, trace)
end
