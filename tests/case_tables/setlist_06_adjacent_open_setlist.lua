-- regress_327_adjacent_open_setlist: 相邻 open SETLIST 保留 vararg 截断、展开与 owner capture
-- unluac: expect-contains [[{ ..., "barrier", ... }]]
-- unluac: expect-not-contains [[unluac error]]
-- unluac: expect-not-contains [[table-set-list]]
-- unluac: expect-ast-count [[local-binding]] [[1]] [[@proto=1]]
-- unluac: expect-ast-count [[local-binding]] [[0]] [[@proto=2]]
-- unluac: expect-ast-count [[table-list-field]] [[3]] [[@proto=1]]
local function build(...)
    local values = { ..., "barrier", ... }
    return function()
        return table.concat(values, ",")
    end
end

local read = build("x", "y")
local result = read()
assert(result == "x,barrier,x,y")
print("regress_327_adjacent_open_setlist", result)

local single = build("one")
local many = build("p", "q", "r")
assert(single() == "one,barrier,one")
assert(many() == "p,barrier,p,q,r")
assert(read() == "x,barrier,x,y")
assert(single() == "one,barrier,one")
print("independent open lists", single(), many(), read())
