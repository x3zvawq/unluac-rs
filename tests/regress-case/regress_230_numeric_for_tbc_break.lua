-- regress_230_numeric_for_tbc_break#1: numeric-for 的 break 由循环词法边界接管 TBC cleanup
local mt = {
    __close = function(value)
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

print("regress_230_numeric_for_tbc_break#done", escaped())
