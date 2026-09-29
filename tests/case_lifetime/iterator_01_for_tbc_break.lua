-- regress_230_numeric_for_tbc_break#1: numeric-for 的 break 由循环词法边界接管 TBC cleanup
-- unluac: expect-ast-count [[local-binding]] [[8]]
-- unluac: expect-ast-count [[close-binding]] [[2]]
-- unluac: expect-ast-count [[numeric-for]] [[1]]
-- unluac: expect-ast-count [[break]] [[1]]
local closed = {}
local mt = {
    __close = function(value, err)
        assert(err == nil)
        if value.tag == "outer" then
            assert(table.concat(closed, ",") == "inner:1,inner:2")
        end
        closed[#closed + 1] = value.tag
        print("regress_230_numeric_for_tbc_break#close", value.tag)
    end,
}

local outer <close> = setmetatable({ tag = "outer" }, mt)
local escaped
for i = 1, 3 do
    local value <close> = setmetatable({ tag = "inner:" .. i }, mt)
    local snapshot = i
    local function read_snapshot()
        return snapshot
    end
    if i == 2 then
        escaped = read_snapshot
        break
    end
    print("regress_230_numeric_for_tbc_break#body", i, value ~= nil, read_snapshot())
end

assert(escaped() == 2)
assert(table.concat(closed, ",") == "inner:1,inner:2")
print("regress_230_numeric_for_tbc_break#done", escaped())
