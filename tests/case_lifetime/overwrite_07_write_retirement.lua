-- __call 在 callee 槽留下函数；Ignore CALL 不会用返回值覆写它。后面的 COPY
-- 即使只改变无逻辑用途的槽，也能决定返回后 caller 的 __index 是否观察到旧函数。
local function across_return()
    local weak = setmetatable({}, {__mode = "v"})
    local meta = {}
    meta.__call = function() meta.__call = nil end
    weak.fn = meta.__call
    local original = debug.getmetatable(1)
    debug.setmetatable(1, meta)
    local seen
    local methods = setmetatable({}, {__index = function()
        collectgarbage("collect")
        collectgarbage("collect")
        seen = type(weak.fn)
        return function() end
    end})
    local function build(x)
        (1)()
        local saved = x
        return x
    end
    collectgarbage("stop")
    build({})
    methods.observe()
    debug.setmetatable(1, original)
    collectgarbage("restart")
    print("across-return", seen)
end

-- 两个词法 epoch 都使用 r1。不能分别依据“下一条 COPY 会覆写”和“上一条
-- COPY 已清除残值”删除两条写；必须让同一事务保留至少一次实际物理覆写。
local function consecutive_copies()
    local weak = setmetatable({}, {__mode = "v"})
    local meta = {}
    meta.__call = function() meta.__call = nil end
    weak.fn = meta.__call
    local original = debug.getmetatable(1)
    debug.setmetatable(1, meta)
    local seen
    local methods = setmetatable({}, {__index = function()
        collectgarbage("collect")
        collectgarbage("collect")
        seen = type(weak.fn)
        return function() end
    end})
    local function build(x)
        (1)()
        do local first = x end
        local saved = x
        return x
    end
    collectgarbage("stop")
    build({})
    methods.observe()
    debug.setmetatable(1, original)
    collectgarbage("restart")
    print("consecutive-copies", seen)
end

across_return()
consecutive_copies()
