-- 原低槽 alias/Boolean 也是 caller 前缀；稳定值不能证明删除声明后原残值位置不变。
-- unluac: expect-not-contains [[unluac error]]
-- unluac: expect-ast-count [[local-binding]] [[5]] [[@proto=1]]
-- unluac: expect-ast-count [[local-binding]] [[5]] [[@proto=6]]
-- unluac: expect-ast-count [[local-binding]] [[0]] [[@proto=3]]
-- unluac: expect-ast-count [[local-binding]] [[0]] [[@proto=8]]
-- unluac: expect-contains [[if weak[2] then]] [[@debug=retained]]
-- unluac: expect-contains [[seen = type(weak[1])]] [[@debug=retained]]

local function not_prefix()
    local weak = setmetatable({}, { __mode = "v" })
    local seen
    local function sink()
        -- 该槽将资源放在下一次调用可覆盖的残值边界。
        local pad0 = 0
        local object = {}
        weak[1] = object
    end
    local methods = setmetatable({}, { __index = function()
        collectgarbage("collect")
        seen = type(weak[1])
        return function() end
    end })
    local function sample(value, sink)
        local inverted = not value
        sink()
        return inverted, inverted
    end
    collectgarbage("collect")
    -- 可选分支确定 caller frame 宽度；基线路径不执行它，也不改写待观察槽。
    if weak[2] then print(0, 1, 2, 3, 4) end
    collectgarbage("stop")
    sample(false, sink)
    methods.observe()
    collectgarbage("restart")
    return seen
end

local function copy_prefix()
    local weak = setmetatable({}, { __mode = "v" })
    local seen
    local function sink()
        -- 该槽将资源放在下一次调用可覆盖的残值边界。
        local pad0 = 0
        local object = {}
        weak[1] = object
    end
    local methods = setmetatable({}, { __index = function()
        collectgarbage("collect")
        seen = type(weak[1])
        return function() end
    end })
    local function sample(sink)
        local source = {}
        local alias = source
        sink(source)
        sink(alias)
        return source, alias
    end
    collectgarbage("collect")
    -- 可选分支确定 caller frame 宽度；基线路径不执行它，也不改写待观察槽。
    if weak[2] then print(0, 1, 2, 3, 4) end
    collectgarbage("stop")
    sample(sink)
    methods.observe()
    collectgarbage("restart")
    return seen
end

local not_seen = not_prefix()
local copy_seen = copy_prefix()
assert(not_seen == "nil", "Boolean prefix removal changed residual roots")
assert(copy_seen == "nil", "copy prefix removal changed residual roots")
print("regress_583_caller_prefix_residuals", not_seen, copy_seen)
