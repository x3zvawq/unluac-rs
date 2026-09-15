-- 计算 key 后读取上值目标，RHS 回调改写同名 cell 不能改变目标表快照。
-- unluac: expect-contains [[.name .. ":" .. tostring(]]
-- unluac: expect-not-contains [[= tostring(]]
local events = {}
local log
local after_name = {}
local after_tostring = {}
local target = setmetatable({}, {
    __newindex = function(self, key, value)
        assert(log == after_tostring, "store must follow tostring")
        events[#events + 1] = "store:" .. key .. ":" .. value
        rawset(self, key, value)
    end,
})
local original = setmetatable({}, {
    __len = function()
        events[#events + 1] = "len"
        log = target
        return 10
    end,
})
local value = setmetatable({}, {
    __index = function(_, key)
        assert(key == "name" and log == target, "name must follow len")
        events[#events + 1] = "name"
        log = after_name
        return "node"
    end,
})
local message = setmetatable({}, {
    __tostring = function()
        assert(log == after_name, "tostring must follow name")
        events[#events + 1] = "tostring"
        log = after_tostring
        return "msg"
    end,
})
local function append(value, message)
    log[#log + 1] = value.name .. ":" .. tostring(message)
end
log = original
append(value, message)
assert(rawget(target, 11) == "node:msg", "base must be captured after key and before RHS")
assert(next(original) == nil and next(after_name) == nil and next(after_tostring) == nil)
assert(table.concat(events, ",") == "len,name,tostring,store:11:node:msg")
print(table.concat(events, ","))
