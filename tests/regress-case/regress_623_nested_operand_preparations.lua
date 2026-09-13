-- 比较左操作数的完整原准备链必须保持原槽，不能让旧 nil/读取作用域延长到右侧 CALL。

-- GETUPVAL 后原位取长度，再准备 tonumber 与内层 CALL。
local function check_length_operand()
    local captured_text = "abcd"
    local weak = setmetatable({}, {__mode = "v"})
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
        if #captured_text < tonumber(make()) then return 1 else return 2 end
    end
    followed()
    setmetatable(_G, old)
end
check_length_operand()

-- GETUPVAL 后原位执行加法，再准备右侧 CALL；字面量不能代替原准备布局。
local function check_arithmetic_operand()
    local captured_number = 2
    local weak = setmetatable({}, {__mode = "v"})
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
        if captured_number + 1 < tonumber(make()) then return 1 else return 2 end
    end
    followed()
    setmetatable(_G, old)
end
check_arithmetic_operand()

-- 以上值为根的两层表读取复用同一原槽，先完成读取再准备右侧 CALL。
local function check_nested_table_operand()
    local holder = {inner = {value = "9.125"}}
    local weak = setmetatable({}, {__mode = "v"})
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
        if holder.inner.value == make() then return 1 else return 2 end
    end
    followed()
    setmetatable(_G, old)
end
check_nested_table_operand()

-- 取长度元方法在原准备时仍须看到旧根，后续 CALL 才结束该根。
local function check_length_metamethod()
    local weak = setmetatable({}, {__mode = "v"})
    local captured_text = setmetatable({}, {__len = function()
        collectgarbage("collect")
        print("left-len-observed", weak[1] ~= nil)
        assert(weak[1] ~= nil, "left LEN released old scope root")
        return 4
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
        if #captured_text < tonumber(make()) then return 1 else return 2 end
    end
    followed()
    setmetatable(_G, old)
end
check_length_metamethod()

-- 加法元方法不得越过右侧 CALL，也不能提前清除旧 scope 的结果。
local function check_arithmetic_metamethod()
    local weak = setmetatable({}, {__mode = "v"})
    local captured_number = setmetatable({}, {__add = function(_, rhs)
        collectgarbage("collect")
        print("left-add-observed", weak[1] ~= nil)
        assert(weak[1] ~= nil, "left ADD released old scope root")
        assert(rhs == 1)
        return 3
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
        if captured_number + 1 < tonumber(make()) then return 1 else return 2 end
    end
    followed()
    setmetatable(_G, old)
end
check_arithmetic_metamethod()

-- 两级索引元方法都在 CALL 前观察旧根，验证字段链的完整执行顺序。
local function check_nested_table_metamethod()
    local weak = setmetatable({}, {__mode = "v"})
    local inner = setmetatable({}, {__index = function(_, key)
        collectgarbage("collect")
        print("inner-index-observed", weak[1] ~= nil)
        assert(weak[1] ~= nil, "inner INDEX released old scope root")
        assert(key == "value")
        return "9.125"
    end})
    local holder = setmetatable({}, {__index = function(_, key)
        collectgarbage("collect")
        print("outer-index-observed", weak[1] ~= nil)
        assert(weak[1] ~= nil, "outer INDEX released old scope root")
        assert(key == "inner")
        return inner
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
        if holder.inner.value == make() then return 1 else return 2 end
    end
    followed()
    setmetatable(_G, old)
end
check_nested_table_metamethod()
