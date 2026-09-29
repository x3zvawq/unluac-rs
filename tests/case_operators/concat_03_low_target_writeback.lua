-- unluac: expect-ast-count [[local-binding]] [[0]] [[@proto=3]] [[@dialect=luajit]]
-- unluac: expect-ast-count [[local-binding]] [[0]] [[@proto=1]] [[@dialect=luau]]
-- unluac: expect-ast-count [[local-binding]] [[0]] [[@proto=1]] [[@dialect=lua5.5]]
-- unluac: expect-ast-count [[local-binding]] [[0]] [[@proto=1]] [[@dialect=lua5.4]]
-- unluac: expect-ast-count [[local-binding]] [[0]] [[@proto=1]] [[@dialect=lua5.3]]
-- unluac: expect-ast-count [[local-binding]] [[0]] [[@proto=1]] [[@dialect=lua5.2]]
-- unluac: expect-ast-count [[local-binding]] [[0]] [[@proto=1]] [[@dialect=lua5.1]]
-- unluac: expect-ast-count [[function]] [[3]]
-- unluac: expect-ast-count [[if]] [[0]]
-- unluac: expect-ast-max [[local-binding]] [[4]]
-- CONCAT 输入从左到右准备、从右到左合并，完整结果再写回已有低槽。
-- unluac: expect-contains [[value = value .. ":" .. right]] [[@debug=retained]]
-- unluac: expect-count [[.. ":" ..]] [[1]]
local function update(value, right)
    value = value .. ":" .. right
    return value
end

local trace = {}
local left = setmetatable({ tag = "left" }, {
    __concat = function(lhs, rhs)
        assert(lhs.tag == "left")
        assert(rhs == ":tail")
        trace[#trace + 1] = "left"
        return "head" .. rhs, "discarded"
    end,
})
local right = setmetatable({ tag = "right" }, {
    __concat = function(lhs, rhs)
        assert(lhs == ":")
        assert(rhs.tag == "right")
        trace[#trace + 1] = "right"
        return ":tail", "discarded"
    end,
})
assert(update(left, right) == "head:tail")
assert(table.concat(trace, ",") == "right,left")
assert(update("plain", "text") == "plain:text")
print("concat-low-target", table.concat(trace, ","))
assert(update("", "") == ":")
assert(update(0, -2) == "0:-2")
assert(update("\0", "x\0") == "\0:x\0")
assert(not pcall(update, false, "text"))
assert(not pcall(update, "head", {}))
assert(table.concat(trace, ",") == "right,left")
-- 右侧已经合并后，左侧类型错误仍须保留右侧的副作用。
assert(not pcall(update, false, right))
assert(table.concat(trace, ",") == "right,left,right")
assert(select("#", update(left, right)) == 1)
assert(table.concat(trace, ",") == "right,left,right,right,left")
assert(select("#", update("", 0)) == 1)
