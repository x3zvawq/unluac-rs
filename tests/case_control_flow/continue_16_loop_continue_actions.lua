-- Luau 的 while continue 跳到入口，repeat continue 则必须求值尾条件。
-- O0/O1 可把跳过剩余循环体恢复为 if；O2 内联后的回边仍需要 continue。
-- unluac: expect-ast-min [[continue]] [[1]] [[@variant=O2]]
-- unluac: expect-ast-min [[while]] [[1]]
-- unluac: expect-ast-min [[repeat]] [[1]]
local function observe(skip, stop)
    local trace = {}
    local i, total = 0, 0
    local function tail(j)
        trace[#trace + 1] = i * 10 + j
        return j == 2
    end
    while i < 4 do
        i = i + 1
        if skip and i % 2 == 0 then
            continue
        end
        local j = 0
        repeat
            j = j + 1
            if skip and j == 1 then
                continue
            end
            total = total + i * 10 + j
        until tail(j)
        if stop and i == 3 then
            break
        end
    end
    return total, table.concat(trace, ","), i
end

local function expected(skip, stop)
    local trace, total = {}, 0
    local last = stop and 3 or 4
    for i = 1, last do
        if not skip or i % 2 ~= 0 then
            for j = 1, 2 do
                if not skip or j ~= 1 then
                    total = total + i * 10 + j
                end
                trace[#trace + 1] = i * 10 + j
            end
        end
    end
    return total, table.concat(trace, ","), last
end

for mode = 0, 3 do
    local skip, stop = mode % 2 == 1, mode >= 2
    local value, trace, last = observe(skip, stop)
    local want_value, want_trace, want_last = expected(skip, stop)
    assert(value == want_value)
    assert(trace == want_trace)
    assert(last == want_last)
    print("luau_03#1", mode, value, trace, last)
end
