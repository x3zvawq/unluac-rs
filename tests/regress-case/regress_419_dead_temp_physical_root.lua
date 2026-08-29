-- regress_419_dead_temp_physical_root: HIR 保留的 dead physical-home copy 必须阻止 AST cleanup 再删除

local function run()
    collectgarbage("stop")
    local weak = setmetatable({}, { __mode = "v" })
    local original = { marker = 42 }
    weak.value = original

    local function callback()
        original = nil
        collectgarbage("restart")
        collectgarbage("collect")
        collectgarbage("collect")
        assert(weak.value ~= nil, "copy root lost")
    end

    local root_copy = original
    callback()
end

local function expires_at_overwrite()
    collectgarbage("stop")
    local weak = setmetatable({}, { __mode = "v" })
    local original = { marker = 84 }
    weak.value = original

    local function clear_original()
        original = nil
    end

    local root_copy = original
    clear_original()
    root_copy = nil
    collectgarbage("restart")
    collectgarbage("collect")
    collectgarbage("collect")
    assert(weak.value == nil, "expired local copy root retained")
end

run()
expires_at_overwrite()
print("regress_419_dead_temp_physical_root", "OK")
