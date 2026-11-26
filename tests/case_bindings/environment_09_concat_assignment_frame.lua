-- 全局/上值写回完整 CONCAT 帧，先完成读取及拼接，再更新目标。
-- unluac: expect-contains [[CONCAT_OUT = CONCAT_IN ..]]
-- unluac: expect-contains [[result = CONCAT_IN .. suffix()]] [[@debug=retained]]
local events = {}
local result = "before"
local phase = "global"
local function record(event)
    events[#events + 1] = phase .. ":" .. event
end
local operand = setmetatable({}, {
    __concat = function(_, right)
        assert(result == "before")
        record("concat:" .. right)
        return "done:" .. right
    end,
})
local function suffix()
    record("suffix")
    return "tail"
end
local function write_global()
    CONCAT_OUT = CONCAT_IN .. suffix()
end
local function write_cell()
    result = CONCAT_IN .. suffix()
end
local previous = getmetatable(_G)
setmetatable(_G, {
    __index = function(_, key)
        assert(key == "CONCAT_IN")
        record("read")
        return operand
    end,
    __newindex = function(_, key, value)
        assert(key == "CONCAT_OUT" and value == "done:tail")
        record("write")
    end,
})
write_global()
phase = "cell"
write_cell()
setmetatable(_G, previous)
assert(result == "done:tail")
assert(table.concat(events, ",") ==
    "global:read,global:suffix,global:concat:tail,global:write,cell:read,cell:suffix,cell:concat:tail")
print("concat-assignment-frame", result, table.concat(events, ","))
