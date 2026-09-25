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
        return "head" .. rhs
    end,
})
local right = setmetatable({ tag = "right" }, {
    __concat = function(lhs, rhs)
        assert(lhs == ":")
        assert(rhs.tag == "right")
        trace[#trace + 1] = "right"
        return ":tail"
    end,
})
assert(update(left, right) == "head:tail")
assert(table.concat(trace, ",") == "right,left")
assert(update("plain", "text") == "plain:text")
print("concat-low-target", table.concat(trace, ","))
