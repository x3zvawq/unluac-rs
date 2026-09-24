-- 返回首项 COPY 与后一项算术同属 RETURN 帧，保留原值身份和元方法次数。
-- unluac: expect-contains [[return value, value + 1]] [[@debug=retained]]
-- unluac: expect-ast-count [[local-decl]] [[0]] [[@proto=1]] [[@dialect=luau]]
local function pair(value)
    return value, value + 1
end

local calls = 0
local object = setmetatable({ tag = "input" }, {
    __add = function(left, right)
        assert(left.tag == "input" and right == 1)
        calls = calls + 1
        left.tag = "observed"
        return 42
    end,
})
local first, second = pair(object)
assert(first == object and first.tag == "observed" and second == 42)
assert(calls == 1)
local a, b = pair(7)
assert(a == 7 and b == 8 and calls == 1)
print("return-arithmetic", first.tag, second, a, b, calls)
