-- COPY 根的三个独立时点：回调期间保活、作用域退出失效、显式 nil 覆写释放。
-- 每个场景保留独立弱表及闭包，避免共享 helper 改变被测 frame。
-- unluac: expect-ast-count [[function]] [[11]]
-- unluac: expect-ast-count [[function]] [[10]] [[@proto=0]]

do
    -- regress_416_copy_local_callback_root: an unread copy local remains a strong root through callback execution

    local weak_values = setmetatable({}, { __mode = "v" })

    local function make()
        local value = {}
        weak_values.value = value
        return value
    end

    local original = make()
    local object = {}

    function object:first()
        return self
    end

    function object:invoke(callback)
        callback()
    end

    local function run()
        local root_copy = original
        local chain = object:first()
        chain:invoke(function()
            original = nil
            collectgarbage("collect")
            collectgarbage("collect")
            assert(weak_values.value ~= nil, "copy root lost during callback")
        end)
    end

    collectgarbage("stop")
    run()
    print("regress_416_copy_local_callback_root", "OK")
end

-- 恢复下一个原独立入口的自动 GC 状态；此时尚未创建该场景的被观测对象。
collectgarbage("restart")

do
    -- regress_416_expired_copy_root: a copy above the restored stack top must expire with its block

    local weak_values = setmetatable({}, { __mode = "v" })

    local function make()
        local value = {}
        weak_values.value = value
        return value
    end

    local original = make()

    local function callback()
        original = nil
        collectgarbage("collect")
        collectgarbage("collect")
        assert(weak_values.value == nil, "expired copy root retained")
    end

    local function run()
        do
            local padding = 1
            local dead_copy = original
        end
        callback()
    end

    collectgarbage("stop")
    run()
    print("regress_416_expired_copy_root", "OK")
end

-- 恢复下一个原独立入口的自动 GC 状态；此时尚未创建该场景的被观测对象。
collectgarbage("restart")

do
    -- regress_417_copy_root_before_overwrite: copy root remains live until its explicit nil overwrite

    local weak_values = setmetatable({}, { __mode = "v" })

    local function make()
        local value = {}
        weak_values.value = value
        return value
    end

    local original = make()

    local function callback()
        original = nil
        collectgarbage("collect")
        collectgarbage("collect")
        assert(weak_values.value ~= nil, "copy root lost before explicit overwrite")
    end

    local function run()
        local root_copy = original
        callback()
        root_copy = nil
        collectgarbage("collect")
        collectgarbage("collect")
        assert(weak_values.value == nil, "copy root retained after explicit overwrite")
    end

    collectgarbage("stop")
    run()
    print("regress_417_copy_root_before_overwrite", "OK")
end
