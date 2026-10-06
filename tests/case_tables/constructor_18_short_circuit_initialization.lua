-- 私有表的字段/批次写属于一次求值；短路关闭时不分配或调用准备函数。
-- unluac: expect-ast-count [[if]] [[0]] [[@proto=1]] [[@dialect=lua5.1]]
-- unluac: expect-ast-count [[if]] [[0]] [[@proto=2]] [[@dialect=lua5.1]]
-- unluac: expect-ast-count [[if]] [[0]] [[@proto=1]] [[@dialect=lua5.2]]
-- unluac: expect-ast-count [[if]] [[0]] [[@proto=2]] [[@dialect=lua5.2]]
-- unluac: expect-ast-count [[if]] [[0]] [[@proto=1]] [[@dialect=lua5.3]]
-- unluac: expect-ast-count [[if]] [[0]] [[@proto=2]] [[@dialect=lua5.3]]
-- unluac: expect-ast-count [[if]] [[0]] [[@proto=1]] [[@dialect=lua5.4]]
-- unluac: expect-ast-count [[if]] [[0]] [[@proto=2]] [[@dialect=lua5.4]]
-- unluac: expect-ast-count [[if]] [[0]] [[@proto=1]] [[@dialect=lua5.5]]
-- unluac: expect-ast-count [[if]] [[0]] [[@proto=2]] [[@dialect=lua5.5]]
-- unluac: expect-ast-count [[if]] [[0]] [[@proto=10]] [[@dialect=luajit]]
-- unluac: expect-ast-count [[if]] [[0]] [[@proto=11]] [[@dialect=luajit]]
-- unluac: expect-ast-count [[local-binding]] [[0]] [[@proto=11]] [[@dialect=luajit]]
-- unluac: expect-ast-count [[local-binding]] [[17]] [[@proto=0]] [[@dialect=luau]]
-- unluac: expect-ast-count [[local-binding]] [[0]] [[@proto=1]] [[@dialect=luau]]
-- unluac: expect-ast-count [[local-binding]] [[0]] [[@proto=2]] [[@dialect=luau]]
-- unluac: expect-ast-count [[if]] [[0]] [[@proto=1]] [[@dialect=luau]]
-- unluac: expect-ast-count [[if]] [[0]] [[@proto=2]] [[@dialect=luau]]
-- unluac: expect-not-contains [[table-set-list]]
local function record(first, consume, key, value)
    return first() == nil and consume({[key()] = value(), tag = "record"}) == nil
end

local function array(first, consume, one, tail)
    return first() == nil and consume({one(), tail()}) == nil
end

local function shared(first, consume)
    if first() then
        local value = {}
        value.self = value
        return consume(value, value)
    end
    return false
end

local events = ""
local enabled = false
local accepted = false
local item = {}
local function first()
    events = events .. "first;"
    if not enabled then return false end
end
local function key()
    events = events .. "key;"
    return accepted and "payload" or "tag"
end
local function value()
    events = events .. "value;"
    return item
end
local function tail()
    events = events .. "tail;"
    return 17, nil, 29
end
local function consume_record(t)
    events = events .. "record;"
    -- 动态键既可新增字段，也可覆盖模板原键；两种情况都必须发生在原模板分配之后。
    if accepted then
        assert(t.payload == item and t.tag == "record" and t[1] == nil)
    else
        -- JIT 在 TDUP 时已装入 tag，其它编译器可在动态键之后写 tag。
        -- 记录各自源码基线的最终身份，不能把一种方言的写入顺序强加给其它方言。
        assert(t.payload == nil and t[1] == nil)
        print("template-collision", t.tag == item, t.tag == "record")
    end
    if not accepted then return false end
end
local function consume_array(t)
    events = events .. "array;"
    assert(t[1] == item and t[2] == 17 and t[3] == nil and t[4] == 29 and t[5] == nil)
    if not accepted then return false end
end
for mask = 0, 3 do
    enabled, accepted = mask % 2 == 1, mask >= 2
    events = ""
    assert(record(first, consume_record, key, value) == (enabled and accepted))
    assert(events == (enabled and "first;key;value;record;" or "first;"))
    events = ""
    assert(array(first, consume_array, value, tail) == (enabled and accepted))
    assert(events == (enabled and "first;value;tail;array;" or "first;"))
    print("constructor decision", mask, events)
end
local count = 0
local function enabled_shared() return enabled end
local function consume_shared(a, b)
    count = count + 1
    assert(a == b and a.self == a)
    return true
end
enabled = false
assert(shared(enabled_shared, consume_shared) == false and count == 0)
enabled = true
assert(shared(enabled_shared, consume_shared) == true and count == 1)
print("shared constructor", count)
