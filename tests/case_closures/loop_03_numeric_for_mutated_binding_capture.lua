-- regress_301_numeric_for_mutated_binding_capture: 赋值后的for binding捕获不能回读header phi
-- unluac: expect-not-contains [[end)(]]
-- unluac: expect-not-contains [[unresolved]]
-- unluac: expect-not-contains [[unluac error]]
-- unluac: expect-contains [[p2_1(function()]] [[@debug=stripped]]
-- unluac: expect-contains [[mutate(function()]] [[@debug=retained]]
-- unluac: expect-ast-count [[empty-local]] [[0]]
local globals = {}
for name in pairs(_G) do
    globals[name] = true
end

local closures = {}
for index = 1, 3 do
    index = index + 10
    closures[#closures + 1] = function()
        return index
    end
end

local function sum_snapshots(limit, mutate)
    local total = 0
    for index = 1, limit do
        local snapshot = index
        total = total + snapshot
        mutate(function()
            index = index + 10
        end)
        total = total + snapshot
    end
    return total
end

local snapshot_total = sum_snapshots(2, function(edit)
    edit()
end)

local leaks = {}
for name in pairs(_G) do
    if not globals[name] then
        leaks[#leaks + 1] = name
    end
end
table.sort(leaks)

assert(closures[1]() == 11 and closures[2]() == 12 and closures[3]() == 13)
assert(snapshot_total == 6 and #leaks == 0)

print(
    "regress_301_numeric_for_mutated_binding_capture",
    closures[1](),
    closures[2](),
    closures[3](),
    snapshot_total,
    table.concat(leaks, ",")
)
