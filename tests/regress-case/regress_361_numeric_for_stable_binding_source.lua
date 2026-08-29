-- regress_361_numeric_for_stable_binding_source: 未被状态准备改写的参数可直接恢复到 numeric-for header
-- unluac: expect-contains [[for r1_2 = p1_0, 1 do]]

local function run(value)
    local start = value
    local keep = math.abs(-9)
    local total = 0
    for index = start, 1 do
        total = total + index
    end
    return total, keep
end

local total, keep = run(1)
assert(total == 1 and keep == 9)
