-- unluac: expect-not-contains [[table-set-list]]
-- 第二次迭代清掉上一行后，循环外的四个 binding 仍逐项保活到各自 COPY。
local weak = setmetatable({}, { __mode = "v" })
local function make(index)
    collectgarbage("collect")
    if index >= 5 then
        for old = 1, 4 do
            assert((weak[old] ~= nil) == (old >= index - 4), "iteration roots")
        end
    end
    local value = { index }
    weak[index] = value
    return value
end
local function clear(rows, index)
    rows[index - 1] = nil
end
local function run()
    local rows = {}
    local first, second, third, fourth
    for index = 1, 2 do
        clear(rows, index)
        first = make(index * 4 - 3)
        second = make(index * 4 - 2)
        third = make(index * 4 - 1)
        fourth = make(index * 4)
        rows[index] = { first, second, third, fourth }
    end
    return rows
end
local rows = run()
assert(rows[1] == nil and rows[2][1][1] == 5 and rows[2][4][1] == 8)
print("iteration roots", rows[2][1][1], rows[2][4][1])
