-- 未暴露的新建子表可合并，持有外部资源或已经暴露的 owner 则不能借此删除独立根。
local weak = setmetatable({}, {__mode = "v"})
local function watch(label)
    return setmetatable({}, {
        __lt = function()
            collectgarbage("collect")
            collectgarbage("collect")
            print(label, weak[1] ~= nil)
            return true
        end,
    })
end
local function make()
    local value = {}
    weak[1] = value
    return value
end

local function payload(value, observer)
    local result = {payload = {value}, marker = 1}
    value = nil
    result.payload = nil
    if observer < observer then return result.marker end
    return 0
end
local function run_payload()
    return payload(make(), watch("payload-root"))
end
assert(run_payload() == 1)

-- 同一条赋值中的写 base 不暴露 owner，但 RHS 读取并传出 owner 会暴露它。
local function expose(result)
    weak[1] = result.labels
    return "exposed"
end
local function escaped(observer)
    local result = {labels = {"raw", "derived"}, marker = 2}
    result.marker = expose(result)
    result.labels = nil
    if observer < observer then return result.marker end
    return "unreachable"
end
assert(escaped(watch("escaped-root")) == "exposed")

local function private(values)
    local result = {first = values[1], labels = {"raw", "derived"}, count = #values}
    for index, value in ipairs(values) do result[value] = index end
    return result
end
local result = private({"labels", "first"})
assert(result.labels == 1 and result.first == 2 and result.count == 2)
local events = {}
local proxy = setmetatable({}, {
    __index = function(_, key)
        events[#events + 1] = "index:" .. tostring(key)
        if key == 1 then return "first" end
    end,
    __len = function()
        events[#events + 1] = "length"
        return 1
    end,
})
local projected = private(proxy)
assert(projected.labels[1] == "raw" and projected.labels[2] == "derived")
print("private-constructor", result.count, projected.count, projected.first, table.concat(events, ","))
