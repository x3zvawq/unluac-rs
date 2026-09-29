-- regress_221_repeat_candidate_identity#1: repeat 必须消费 Structure 已选中的完整短路候选
-- unluac: expect-contains [[repeat]]
-- unluac: expect-contains [[for ]]
-- unluac: expect-not-contains [[goto ]]
-- unluac: expect-not-contains [[::L]]
-- unluac: expect-not-contains [[unresolved]]
-- unluac: expect-not-contains [[unluac error]]
-- unluac: expect-not-contains [[local r1_0]]
-- unluac: expect-not-contains [[r1_0 = p1_2]]
-- unluac: expect-not-contains [[p1_2 = r1_0]]
-- unluac: expect-not-contains [[local r2_0]] [[@dialect=luajit]]
-- unluac: expect-not-contains [[r2_0 = p2_2]] [[@dialect=luajit]]
-- unluac: expect-not-contains [[p2_2 = r2_0]] [[@dialect=luajit]]
-- unluac: expect-contains [[return p1_2]] [[@dialect=lua5.1]]
-- unluac: expect-contains [[return p1_2]] [[@dialect=lua5.2]]
-- unluac: expect-contains [[return p1_2]] [[@dialect=lua5.3]]
-- unluac: expect-contains [[return p1_2]] [[@dialect=lua5.4]]
-- unluac: expect-contains [[return p1_2]] [[@dialect=lua5.5]]
-- unluac: expect-contains [[return p2_2]] [[@dialect=luajit]]
-- unluac: expect-ast-count [[repeat]] [[1]]
-- unluac: expect-ast-count [[numeric-for]] [[1]]
-- unluac: expect-ast-count [[local-binding]] [[4]]
local function run(a, b, value)
    repeat
        for index = 1, 2 do
            value = value + index
        end
    until a and b
    return value
end

assert(run(true, true, 0) == 3)
assert(run(0, "", -3) == 0)
assert(run("", 0, 10) == 13)
local trace = {}
local value = setmetatable({}, {
    __add = function(left, right)
        trace[#trace + 1] = right
        assert(#trace < 5, "observed repeat backedge")
        return left
    end,
})
assert(run(true, true, value) == value)
assert(table.concat(trace, ",") == "1,2")
trace = {}
assert(not pcall(run, false, true, value))
assert(table.concat(trace, ",") == "1,2,1,2,1")
trace = {}
assert(not pcall(run, true, nil, value))
assert(table.concat(trace, ",") == "1,2,1,2,1")
print("regress_221_repeat_candidate_identity#1", run(true, true, 0))
