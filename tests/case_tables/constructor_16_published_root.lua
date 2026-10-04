-- 字段发布后清空唯一外部引用，原低槽表仍应保活至调用返回。
-- unluac: expect-ast-max [[local-binding]] [[4]] [[@proto=5]] [[@dialect=lua5.1]]
-- unluac: expect-ast-max [[local-binding]] [[4]] [[@proto=5]] [[@dialect=lua5.2]]
-- unluac: expect-ast-max [[local-binding]] [[4]] [[@proto=5]] [[@dialect=lua5.3]]
-- unluac: expect-ast-max [[local-binding]] [[4]] [[@proto=5]] [[@dialect=lua5.4]]
-- unluac: expect-ast-max [[local-binding]] [[4]] [[@proto=5]] [[@dialect=lua5.5]]
-- unluac: expect-ast-max [[local-binding]] [[4]] [[@proto=1]] [[@dialect=luajit]]
local weak = setmetatable({}, {__mode = "v"})
local events, observed = {}, 0
local function consume(outer, middle)
    assert(middle == "middle")
    outer.child = nil
    collectgarbage("collect")
    assert(weak[1] ~= nil and weak[1].tag == "inner")
    observed = observed + 1
end
local function make_outer()
    return setmetatable({}, {__newindex = function(t, k, v)
        assert(k == "child")
        weak[1] = v
        rawset(t, k, v)
    end})
end
local function mark(name)
    events[#events + 1] = name
    return name
end
local function run()
    local callee = consume
    local outer = make_outer()
    local middle = mark("middle")
    local inner = {tag = mark("inner")}
    outer.child = inner
    callee(outer, middle)
end
run()
run()
assert(observed == 2 and table.concat(events, ",") == "middle,inner,middle,inner")
print("constructor-published-root", observed)
