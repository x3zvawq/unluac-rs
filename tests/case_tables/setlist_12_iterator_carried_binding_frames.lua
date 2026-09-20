-- unluac: expect-not-contains [[table-set-list]]
-- unluac: expect-ast-count [[table-list-field]] [[2]] [[@proto=1]] [[@dialect=lua5.1]]
-- unluac: expect-ast-count [[table-list-field]] [[2]] [[@proto=1]] [[@dialect=lua5.4]]
-- unluac: expect-ast-count [[table-list-field]] [[2]] [[@proto=1]] [[@dialect=luau]]
-- 列表准备和 iterator 结果必须共同恢复，循环携带的 sum 不应截断构造事务。
local function total(Activity)
    local sum = 0
    for _, v in ipairs({Activity.IDS.M_BOX_1.ID, Activity.IDS.M_BOX_2.ID}) do
        sum = sum + v
    end
    return sum
end

local trace = {}
local values = {3, 7}
local boxes = {}
for index = 1, 2 do
    boxes["M_BOX_" .. index] = setmetatable({}, {
        __index = function(_, key)
            trace[#trace + 1] = index .. ":" .. key
            return values[index]
        end,
    })
end
local activity = setmetatable({}, {
    __index = function(_, key)
        trace[#trace + 1] = key
        return boxes
    end,
})
assert(total(activity) == 10)
assert(table.concat(trace, ",") == "IDS,1:ID,IDS,2:ID")
values[1], values[2] = -2, 11
assert(total(activity) == 9)
print("iterator frames", table.concat(trace, ","))
