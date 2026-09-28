-- 完整索引赋值保持各 VM 的目标读取时点、CALL 单结果宽度与匿名 CLOSURE 返回槽。
-- unluac: expect-ast-count [[local-decl]] [[0]] [[@proto=1]] [[@dialect=lua5.1]]
-- unluac: expect-ast-count [[local-decl]] [[0]] [[@proto=1]] [[@dialect=lua5.2]]
-- unluac: expect-ast-count [[local-decl]] [[0]] [[@proto=1]] [[@dialect=lua5.3]]
-- unluac: expect-ast-count [[local-decl]] [[0]] [[@proto=1]] [[@dialect=lua5.4]]
-- unluac: expect-ast-count [[local-decl]] [[0]] [[@proto=1]] [[@dialect=lua5.5]]
-- unluac: expect-ast-count [[function]] [[1]] [[@proto=1]] [[@dialect=lua5.1]]
-- unluac: expect-ast-count [[function]] [[1]] [[@proto=1]] [[@dialect=lua5.2]]
-- unluac: expect-ast-count [[function]] [[1]] [[@proto=1]] [[@dialect=lua5.3]]
-- unluac: expect-ast-count [[function]] [[1]] [[@proto=1]] [[@dialect=lua5.4]]
-- unluac: expect-ast-count [[function]] [[1]] [[@proto=1]] [[@dialect=lua5.5]]
-- unluac: expect-ast-count [[local-decl]] [[0]] [[@proto=4]] [[@dialect=lua5.1]]
-- unluac: expect-ast-count [[local-decl]] [[0]] [[@proto=4]] [[@dialect=lua5.2]]
-- unluac: expect-ast-count [[local-decl]] [[0]] [[@proto=4]] [[@dialect=lua5.3]]
-- unluac: expect-ast-count [[local-decl]] [[0]] [[@proto=4]] [[@dialect=lua5.4]]
-- unluac: expect-ast-count [[local-decl]] [[0]] [[@proto=4]] [[@dialect=lua5.5]]
-- unluac: expect-ast-max [[local-decl]] [[12]] [[@proto=0]]
-- unluac: expect-ast-count [[local-decl]] [[0]] [[@proto=8]] [[@dialect=luajit]]
-- unluac: expect-ast-count [[function]] [[1]] [[@proto=8]] [[@dialect=luajit]]
-- unluac: expect-ast-count [[local-decl]] [[0]] [[@proto=6]] [[@dialect=luajit]]
local target, rhs
local function append()
    target[#target + 1] = rhs()
    return function() end
end

-- 显式快照必须始终写旧目标，不能跟随 RHS 更换的同名 cell。
-- unluac: expect-ast-min [[local-decl]] [[1]] [[@proto=3]] [[@dialect=lua5.2]]
-- unluac: expect-ast-min [[local-decl]] [[1]] [[@proto=3]] [[@dialect=lua5.3]]
-- unluac: expect-ast-min [[local-decl]] [[1]] [[@proto=3]] [[@dialect=lua5.4]]
-- unluac: expect-ast-min [[local-decl]] [[1]] [[@proto=3]] [[@dialect=lua5.5]]
local function explicit_snapshot()
    local chosen = target
    local index = #target + 1
    chosen[index] = rhs()
end

local function fixed_key()
    target.value = rhs()
end

local events = {}
local middle, last
local proxy_factory = rawget(_G, "newproxy")
local function observed(name)
    local metatable = {
        __len = function()
            events[#events + 1] = "len:" .. name
            target = middle
            return 10
        end,
        __newindex = function(_, key, value)
            assert((key == 11 or key == "value") and value == "value")
            events[#events + 1] = "store:" .. name
        end,
    }
    if proxy_factory then
        local proxy = proxy_factory(true)
        local actual = getmetatable(proxy)
        actual.__len = metatable.__len
        actual.__newindex = metatable.__newindex
        return proxy
    end
    return setmetatable({}, metatable)
end
local original = observed("original")
middle = observed("middle")
last = observed("last")
rhs = function()
    assert(target == middle)
    events[#events + 1] = "rhs"
    target = last
    return "value", "ignored"
end

target = original
assert(type(append()) == "function")
local expected = "middle"
if _VERSION == "Lua 5.1" then
    expected = "original"
elseif _VERSION == "Lua 5.2" or _VERSION == "Lua 5.3" then
    expected = "last"
end
assert(table.concat(events, ",") == "len:original,rhs,store:" .. expected)
print(table.concat(events, ","))

events = {}
target = original
explicit_snapshot()
assert(table.concat(events, ",") == "len:original,rhs,store:original")
print(table.concat(events, ","))

-- 固定 key 的 SETTABLE 先快照目标，SETTABUP 则在 RHS 之后读取原 upvalue cell。
events = {}
target = original
rhs = function()
    assert(target == original)
    events[#events + 1] = "rhs"
    target = last
    return "value", "ignored"
end
fixed_key()
expected = _VERSION == "Lua 5.1" and "original" or "last"
assert(table.concat(events, ",") == "rhs,store:" .. expected)
print(table.concat(events, ","))
