-- 原 nil 声明前缀与 CONCAT 输入 COPY 共同结束旧全局读取的 scratch 根。
-- 字符串前缀保留、词法末端及后缀构造器必须由同一原帧事务验证。
local weak = setmetatable({}, { __mode = "v" })
local events = {}
local previous = getmetatable(_G)
local left = setmetatable({}, {
    __concat = function(_, suffix)
        collectgarbage("collect")
        events[#events + 1] = tostring(weak[1] ~= nil)
        assert(weak[1] == nil, "CONCAT input COPY must overwrite the old scratch root")
        return "slot_" .. suffix
    end,
})
setmetatable(_G, {
    __index = function(_, name)
        if name == "concat_prefix_dead_value" then
            local value = {}
            weak[1] = value
            return value
        end
        if previous and previous.__index then
            local index = previous.__index
            if type(index) == "function" then return index(_G, name) end
            return index[name]
        end
    end,
})
local function check()
    local suffix = "tail"
    do
        local cleared = nil
        local value = concat_prefix_dead_value
    end
    local key = left .. suffix
    local t = { list = { 10, 20, 30 }, meta = { [key] = 7 } }
    assert(t.meta.slot_tail == 7 and t.list[3] == 30)
end
check()
setmetatable(_G, previous)
assert(table.concat(events, ",") == "false")
print("concat-prefix", table.concat(events, ","))
