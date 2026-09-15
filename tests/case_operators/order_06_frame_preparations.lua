-- 条件左侧的完整准备帧必须按原顺序复用槽，不能把旧读取结果保留到观察 CALL。
-- unluac: expect-ast-count [[numeric-for]] [[6]]

-- 动态上值键先准备到 r1，再把上值表准备到 r0；GETTABLE r0,r0,r1 后才调用右侧。
local function check_dynamic_key()
    local weak = setmetatable({}, {__mode = "v"})
    local holder = {value = "9.125"}
    local key = "value"
    local calls = 0
    local old = getmetatable(_G)
    local function make()
        calls = calls + 1
        if calls == 2 then
            collectgarbage("collect")
            print("scope-observed-value", weak[1] ~= nil)
            assert(weak[1] == nil, "old scope result remains rooted")
        end
        return "9.125"
    end
    setmetatable(_G, {__index = function(_, key)
        if key == "for_skip_observe" then
            weak[1] = {}
            return weak[1]
        end
    end})
    local function followed()
        for index = make(), 1, 1 do error("entered") end
        do
            local cleared = nil
            local observed = for_skip_observe
        end
        if holder[key] == make() then return 1 else return 2 end
    end
    followed()
    setmetatable(_G, old)
end
check_dynamic_key()

-- 拼接先把字面量写入 r0、上值写入 r1，再由 CONCAT r0,2 原位写回。
local function check_concat_operand()
    local weak = setmetatable({}, {__mode = "v"})
    local captured = "125"
    local calls = 0
    local old = getmetatable(_G)
    local function make()
        calls = calls + 1
        if calls == 2 then
            collectgarbage("collect")
            print("scope-observed-value", weak[1] ~= nil)
            assert(weak[1] == nil, "old scope result remains rooted")
        end
        return "9.125"
    end
    setmetatable(_G, {__index = function(_, key)
        if key == "for_skip_observe" then
            weak[1] = {}
            return weak[1]
        end
    end})
    local function followed()
        for index = make(), 1, 1 do error("entered") end
        do
            local cleared = nil
            local observed = for_skip_observe
        end
        if "9." .. captured == make() then return 1 else return 2 end
    end
    followed()
    setmetatable(_G, old)
end
check_concat_operand()

-- 上值 receiver 先写入 r0；SELF r0,r0 同时生成 callee r0 与隐式 receiver r1。
local function check_method_operand()
    local weak = setmetatable({}, {__mode = "v"})
    local holder = {value = function(self)
        collectgarbage("collect")
        print("method-observed", weak[1] ~= nil)
        return "9.125"
    end}
    local calls = 0
    local old = getmetatable(_G)
    local function make()
        calls = calls + 1
        if calls == 2 then
            collectgarbage("collect")
            print("scope-observed-value", weak[1] ~= nil)
            assert(weak[1] == nil, "old scope result remains rooted")
        end
        return "9.125"
    end
    setmetatable(_G, {__index = function(_, key)
        if key == "for_skip_observe" then
            weak[1] = {}
            return weak[1]
        end
    end})
    local function followed()
        for index = make(), 1, 1 do error("entered") end
        do
            local cleared = nil
            local observed = for_skip_observe
        end
        if holder:value() == make() then return 1 else return 2 end
    end
    followed()
    setmetatable(_G, old)
end
check_method_operand()

-- 动态 key 和 base 均准备后，索引元方法与后续 CALL 都应看到旧根已释放。
local function check_dynamic_key_metamethod()
    local weak = setmetatable({}, {__mode = "v"})
    local holder = setmetatable({}, {__index = function(_, key)
        collectgarbage("collect")
        print("dynamic-index-observed", weak[1] ~= nil)
        assert(weak[1] == nil, "dynamic key frame kept old root")
        assert(key == "value")
        return "9.125"
    end})
    local key = "value"
    local calls = 0
    local old = getmetatable(_G)
    local function make()
        calls = calls + 1
        if calls == 2 then
            collectgarbage("collect")
            print("scope-observed-value", weak[1] ~= nil)
            assert(weak[1] == nil, "old scope result remains rooted")
        end
        return "9.125"
    end
    setmetatable(_G, {__index = function(_, key)
        if key == "for_skip_observe" then
            weak[1] = {}
            return weak[1]
        end
    end})
    local function followed()
        for index = make(), 1, 1 do error("entered") end
        do
            local cleared = nil
            local observed = for_skip_observe
        end
        if holder[key] == make() then return 1 else return 2 end
    end
    followed()
    setmetatable(_G, old)
end
check_dynamic_key_metamethod()

-- 完整拼接缓冲区覆写旧根后，拼接元方法与后续 CALL 都观察 false。
local function check_concat_metamethod()
    local weak = setmetatable({}, {__mode = "v"})
    local captured = setmetatable({}, {__concat = function(lhs, rhs)
        collectgarbage("collect")
        print("concat-observed", weak[1] ~= nil)
        assert(weak[1] == nil, "concat frame kept old root")
        assert(lhs == "9.")
        return "9.125"
    end})
    local calls = 0
    local old = getmetatable(_G)
    local function make()
        calls = calls + 1
        if calls == 2 then
            collectgarbage("collect")
            print("scope-observed-value", weak[1] ~= nil)
            assert(weak[1] == nil, "old scope result remains rooted")
        end
        return "9.125"
    end
    setmetatable(_G, {__index = function(_, key)
        if key == "for_skip_observe" then
            weak[1] = {}
            return weak[1]
        end
    end})
    local function followed()
        for index = make(), 1, 1 do error("entered") end
        do
            local cleared = nil
            local observed = for_skip_observe
        end
        if "9." .. captured == make() then return 1 else return 2 end
    end
    followed()
    setmetatable(_G, old)
end
check_concat_metamethod()

-- SELF 的字段元方法、方法 CALL 和右侧 CALL 都在原 receiver 写入后观察旧根。
local function check_method_metamethod()
    local weak = setmetatable({}, {__mode = "v"})
    local holder = setmetatable({}, {__index = function(_, key)
        collectgarbage("collect")
        print("self-index-observed", weak[1] ~= nil)
        assert(weak[1] == nil, "SELF frame kept old root")
        assert(key == "value")
        return function(self)
            collectgarbage("collect")
            print("method-observed", weak[1] ~= nil)
            assert(weak[1] == nil, "method CALL kept old root")
            return "9.125"
        end
    end})
    local calls = 0
    local old = getmetatable(_G)
    local function make()
        calls = calls + 1
        if calls == 2 then
            collectgarbage("collect")
            print("scope-observed-value", weak[1] ~= nil)
            assert(weak[1] == nil, "old scope result remains rooted")
        end
        return "9.125"
    end
    setmetatable(_G, {__index = function(_, key)
        if key == "for_skip_observe" then
            weak[1] = {}
            return weak[1]
        end
    end})
    local function followed()
        for index = make(), 1, 1 do error("entered") end
        do
            local cleared = nil
            local observed = for_skip_observe
        end
        if holder:value() == make() then return 1 else return 2 end
    end
    followed()
    setmetatable(_G, old)
end
check_method_metamethod()
