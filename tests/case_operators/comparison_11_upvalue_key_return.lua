-- 短路返回中上值键与上值比较各自保留读取位置，条件右臂不能提前执行索引。
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

-- 检查严格 Boolean 比较，不能把 == true / ~= true 改成一般真值测试。
names.present = 0
observe("present", "missing", false, "")
trace = {}
assert(named_check(names) == false and #trace == 0)
names.present = ""
observe("present", "missing", false, "")
names.present = true
observe("present", "missing", true, "missing")
names.missing = 0
observe("present", "missing", true, "")
names.missing = ""
observe("present", "missing", true, "")
names.missing = true
observe("present", "missing", false, "")
trace = {}
assert(named_check(names) == false and #trace == 0)
names.present, names.missing = nil, nil
trace = {}
assert(select("#", named_check(names)) == 1)
assert(table.concat(trace, ",") == "present,missing")
assert(select("#", observe("present", nil, true, "present")) == 0)

-- 复用索引观察器记录 nil 字段写；各方言的原写入次序由运行输出比较固定。
setmetatable(names, {__newindex = getmetatable(names).__index})
trace = {}
names.first, names.second = nil, nil
assert(#trace == 2)
print("nil-pair-write-order", table.concat(trace, ","))
