-- unluac: expect-not-contains [[table-set-list]]
-- unluac: expect-ast-count [[table-list-field]] [[4]] [[@proto=2]] [[@dialect=lua5.1]]
local weak = setmetatable({}, { __mode = "v" })
local events = {}
function ProducePair(index)
    collectgarbage("collect")
    if index > 1 then
        local previous = (index - 2) * 2
        events[#events + 1] = tostring(weak[previous + 1] ~= nil) .. ":" .. tostring(weak[previous + 2] ~= nil)
    end
    local left = { value = index * 10 }
    local right = { value = index }
    weak[(index - 1) * 2 + 1] = left
    weak[(index - 1) * 2 + 2] = right
    return left, right
end
local function collectRows(self)
    local basis = { 11, 12 }
    local fraction, integer
    local result = {}
    for index = 1, 3 do
        integer, fraction = ProducePair(index)
        if index ~= 2 then
            table.insert(result, { integer.value, fraction.value })
        end
    end
    return result, basis
end
local result, basis = collectRows({})
assert(basis[1] == 11 and basis[2] == 12)
assert(table.concat(result[1], ",") == "10,1")
assert(table.concat(result[2], ",") == "30,3")
assert(table.concat(events, ",") == "true:true,true:true")
collectgarbage("collect")
assert(next(weak) == nil)
print("multi-loop-roots", table.concat(events, ","), table.concat(result[2], ","))

function NextIndex(_, previous)
    collectgarbage("collect")
    if previous > 0 then
        local offset = (previous - 1) * 2
        events[#events + 1] = tostring(weak[offset + 1] ~= nil) .. ":" .. tostring(weak[offset + 2] ~= nil)
    end
    if previous < 3 then return previous + 1 end
end
local function collectGenericRows()
    local left, unused, right
    local rows = {}
    for index in NextIndex, nil, 0 do
        left, right = ProducePair(index)
        if index ~= 2 then
            table.insert(rows, { left.value, right.value })
        end
    end
    return rows
end
events = {}
local generic_rows = collectGenericRows()
assert(table.concat(generic_rows[1], ",") == "10,1")
assert(table.concat(generic_rows[2], ",") == "30,3")
assert(table.concat(events, ",") == "true:true,true:true,true:true,true:true,true:true")
collectgarbage("collect")
assert(next(weak) == nil)
print("generic-dispatch-roots", table.concat(events, ","))
