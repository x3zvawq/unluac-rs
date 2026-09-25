-- 短路返回中上值键与上值比较各自保留读取位置，条件右臂不能提前执行索引。
-- unluac: expect-contains [[== true and (]]
-- unluac: expect-ast-count [[if]] [[0]]
-- unluac: expect-ast-count [[local-binding]] [[0]] [[@proto=2]] [[@dialect=lua5.1]]
-- unluac: expect-ast-count [[local-binding]] [[0]] [[@proto=2]] [[@dialect=lua5.2]]
-- unluac: expect-ast-count [[local-binding]] [[0]] [[@proto=2]] [[@dialect=lua5.3]]
-- unluac: expect-ast-count [[local-binding]] [[0]] [[@proto=2]] [[@dialect=lua5.4]]
-- unluac: expect-ast-count [[local-binding]] [[0]] [[@proto=2]] [[@dialect=lua5.5]]
-- unluac: expect-ast-count [[local-binding]] [[0]] [[@proto=2]] [[@dialect=luau]]
-- unluac: expect-ast-count [[local-binding]] [[0]] [[@proto=6]] [[@dialect=luajit]]
-- unluac: expect-ast-count [[local-binding]] [[1]] [[@proto=6]] [[@dialect=luau]] [[@debug=retained]]
-- unluac: expect-contains [[local matched = names[expected] == true and (forbidden == nil or names[forbidden] ~= true)]] [[@debug=retained]]
local function make_check(expected, forbidden)
    return function(names)
        return names[expected] == true and (forbidden == nil or names[forbidden] ~= true)
    end
end

local trace = {}
local names = setmetatable({}, {
    __index = function(_, key)
        trace[#trace + 1] = key
        return key == "present"
    end,
})

local function observe(expected, forbidden, result, reads)
    trace = {}
    local check = make_check(expected, forbidden)
    assert(check(names) == result)
    assert(table.concat(trace, ",") == reads)
    print("upvalue-key-return", result, table.concat(trace, ","))
end

observe("present", "missing", true, "present,missing")
observe("present", "present", false, "present,present")
observe("present", nil, true, "present")
observe("missing", "present", false, "missing")

local function make_named_check(expected, forbidden)
    return function(names)
        local matched = names[expected] == true and (forbidden == nil or names[forbidden] ~= true)
        return matched
    end
end

local named_check = make_named_check("present", "missing")
trace = {}
assert(named_check(names))
assert(table.concat(trace, ",") == "present,missing")
print("named-upvalue-key-return", table.concat(trace, ","))
