-- regress_180_numeric_for_shared_tail#1: 分支汇入 numeric-for 共享尾时不能提前 continue

local function run(n, value, cond)
    local sink = {}
    for _ = 0, n - 1 do
        local current = value
        if current == 1 then
            sink[1] = cond and 2 or 3
        elseif current == 2 then
            sink[1] = 4
        end
        value = value + 1
    end
    return value, sink[1]
end

print("regress_180_numeric_for_shared_tail#1", run(1, 2, true))
