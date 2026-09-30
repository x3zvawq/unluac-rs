-- 共享 frame-end root 可以交接，但 source 快照和 callback 原调用帧仍须分别证明。
-- PUC stripped 用 callee 别名保留末次调用入口；JIT 的入口残值要求保留原覆盖前缀。
-- unluac: expect-ast-count [[local-binding]] [[2]] [[@proto=1]] [[@dialect=lua5.1]]
-- unluac: expect-ast-count [[local-binding]] [[2]] [[@proto=1]] [[@dialect=lua5.2]]
-- unluac: expect-ast-count [[local-binding]] [[2]] [[@proto=1]] [[@dialect=lua5.3]]
-- unluac: expect-ast-count [[local-binding]] [[2]] [[@proto=1]] [[@dialect=lua5.4]] [[@debug=stripped]]
-- unluac: expect-ast-count [[local-binding]] [[2]] [[@proto=1]] [[@dialect=lua5.5]]
-- unluac: expect-ast-count [[local-binding]] [[3]] [[@proto=5]] [[@dialect=luajit]]
-- unluac: expect-ast-count [[local-binding]] [[3]] [[@proto=1]] [[@debug=retained]]
-- unluac: expect-ast-max [[local-binding]] [[20]]
-- unluac: expect-ast-count [[function]] [[5]]
-- unluac: expect-ast-count [[if]] [[1]]
-- callback 内的临时对象会留在返回后的物理栈中；上层覆写低槽再观察其释放窗口。
-- 动态编译固定 caller，避免被测反编译器同时改变观察者的槽布局。
local held = {}
local weak = setmetatable({ value = held }, { __mode = "v" })
local calls = 0

local function retain(callback)
    local source = held
    held = nil
    local duplicate = source
    -- 子块内联先改变 HIR；随后删除 dead copy 时必须查询当前 home 写入快照。
    if callback then
        local n = 1 + 1
        assert(n == 2)
    end
    callback()
end

retain(function()
    collectgarbage("collect")
    collectgarbage("collect")
    assert(weak.value ~= nil, "scope-end owner disappeared with its dead copy")
    calls = calls + 1
end)
collectgarbage("collect")
collectgarbage("collect")
assert(weak.value == nil, "scope-end owner escaped its function lifetime")
assert(calls == 1)
print("regress_465_scope_end_copy_root_coverage", "OK")

do
    local residue = setmetatable({}, {__mode = "v"})
    local seen
    local function remember()
        local object = {}
        residue.value = object
    end
    local methods = setmetatable({}, {__index = function()
        collectgarbage("collect")
        collectgarbage("collect")
        seen = type(residue.value)
        return function() end
    end})
    local declaration = jit and "local a,b,c,d,e,f=1,1,1,1,1,1"
        or (_VERSION == "Lua 5.1" and "local a,b,c,d=1,1,1,1" or "local a,b,c,d,e=1,1,1,1,1")
    local program = "return function(remember, methods) return function(callback) callback(remember); %s; " ..
        "methods.observe(); local reserve={1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16}; return reserve[1] end end"
    local code = string.format(program, declaration)
    local compile = loadstring or load
    local factory_chunk = assert(compile(code))
    local factory = factory_chunk()
    local observe = factory(remember, methods)
    collectgarbage("stop")
    local result = observe(retain)
    assert(result == 1)
    collectgarbage("restart")
    assert(seen == "table", "callback frame lost its residual root window")
    print("scope-end-callback-residue", seen)
end
