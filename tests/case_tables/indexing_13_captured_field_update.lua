-- 直接上值字段读取进入算术帧，写回之后仍执行原字段读取，不能复用算术结果。
-- unluac: expect-ast-count [[local-binding]] [[0]] [[@proto=1]] [[@dialect=lua5.1]]
-- unluac: expect-ast-count [[local-binding]] [[0]] [[@proto=1]] [[@dialect=lua5.2]]
-- unluac: expect-ast-count [[local-binding]] [[0]] [[@proto=1]] [[@dialect=lua5.3]]
-- unluac: expect-ast-count [[local-binding]] [[0]] [[@proto=1]] [[@dialect=lua5.4]]
-- unluac: expect-ast-count [[local-binding]] [[0]] [[@proto=1]] [[@dialect=lua5.5]]
-- unluac: expect-ast-count [[local-binding]] [[0]] [[@proto=1]] [[@dialect=luau]]
-- unluac: expect-ast-count [[local-binding]] [[0]] [[@proto=8]] [[@dialect=luajit]]
-- unluac: expect-contains [[state.current = state.current + (step or 1)]] [[@debug=retained]]
-- unluac: expect-ast-count [[local-binding]] [[9]] [[@proto=0]]
-- unluac: expect-contains [[local result = update(2)]] [[@debug=retained]]
-- unluac: expect-contains [[update_selected(-1)]] [[@debug=retained]]
-- unluac: expect-ast-count [[assign]] [[9]] [[@proto=0]] [[@dialect=lua5.1]]
-- unluac: expect-ast-count [[assign]] [[9]] [[@proto=0]] [[@dialect=lua5.2]]
-- unluac: expect-ast-count [[assign]] [[9]] [[@proto=0]] [[@dialect=lua5.3]]
-- unluac: expect-ast-count [[assign]] [[9]] [[@proto=0]] [[@dialect=lua5.4]]
-- unluac: expect-ast-count [[assign]] [[9]] [[@proto=0]] [[@dialect=lua5.5]]
-- unluac: expect-ast-count [[assign]] [[9]] [[@proto=0]] [[@dialect=luajit]]
-- unluac: expect-ast-count [[assign]] [[10]] [[@proto=0]] [[@dialect=luau]]
local state = {current = 1}
local function update(step)
    state.current = state.current + (step or 1)
    return state.current
end
assert(update() == 2)
assert(update(false) == 3)
assert(update(4) == 7)

local events = {}
local current = 10
state = setmetatable({}, {
    __index = function(_, key)
        assert(key == "current")
        events[#events + 1] = "read"
        return current
    end,
    __newindex = function(_, key, value)
        assert(key == "current")
        events[#events + 1] = "write"
        current = value + 100
    end,
})
assert(update(2) == 112)
assert(table.concat(events, ",") == "read,write,read")
print("captured-field-update", current, table.concat(events, ","))

-- 不同 VM 的目标快照协议以各自源码执行为基线；读取回调可替换上值中的表。
-- 重编译必须仍向原协议选定的目标写入，随后读取替换后的当前表。
events = {}
local replacement = setmetatable({}, {
    __index = function() return 40 end,
    __newindex = function(_, _, value)
        events[#events + 1] = "replacement:" .. value
    end,
})
state = setmetatable({}, {
    __index = function()
        state = replacement
        events[#events + 1] = "switch"
        return current
    end,
    __newindex = function(_, _, value)
        events[#events + 1] = "original:" .. value
    end,
})
current = 10
local original = state
local result = update(2)
assert(result == 40)
print("target-snapshot", result, table.concat(events, ","))

-- GETTABLE 的结果经 OR 合流后参加算术；读取回调改写上值，不能重读新表或重复读取。
-- unluac: expect-ast-count [[local-binding]] [[0]] [[@proto=8]] [[@dialect=luau]]
-- unluac: expect-ast-count [[local-binding]] [[0]] [[@proto=8]] [[@dialect=lua5.5]]
-- unluac: expect-contains [=[state[key] = (state[key] or 0) + 1]=] [[@debug=retained]] [[@dialect=luau]]
local function update_selected(key, ...)
    state[key] = (state[key] or 0) + 1
end
for selection = 1, 4 do
    current = 10
    if selection == 1 then current = nil
    elseif selection == 2 then current = false
    elseif selection == 3 then current = 0 end
    state, events = original, {}
    update_selected(-1)
    assert(state == replacement and #events == 2 and events[1] == "switch")
    -- 各 VM 的目标读取时点不同；源码/产物输出比较固定实际写入对象和算术结果。
    print("selected-target-snapshot", selection, table.concat(events, ","))
end
