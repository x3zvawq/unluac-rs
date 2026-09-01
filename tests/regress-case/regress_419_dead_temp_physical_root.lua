-- regress_419_dead_temp_physical_root: HIR 保留的 dead physical-home copy 必须阻止 AST cleanup 再删除
-- unluac: expect-contains [[no_event_callable()]]

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

local function global_callee_keeps_independent_root()
    collectgarbage("stop")
    local weak = setmetatable({}, { __mode = "v" })
    local function make_owner()
        return setmetatable({}, {
            __call = function()
                global_callable = nil
            end,
        })
    end

    local owner = make_owner()
    weak.value = owner
    global_callable = owner
    owner = nil

    local callee = global_callable
    callee()
    collectgarbage("restart")
    collectgarbage("collect")
    collectgarbage("collect")
    assert(weak.value ~= nil, "global callee root lost")
end

local function global_callee_without_later_observation_stays_inlineable()
    no_event_callable = function()
        no_event_callable = nil
    end
    local callee = no_event_callable
    callee()
end

run()
expires_at_overwrite()
global_callee_keeps_independent_root()
global_callee_without_later_observation_stays_inlineable()
print("regress_419_dead_temp_physical_root", "OK")
