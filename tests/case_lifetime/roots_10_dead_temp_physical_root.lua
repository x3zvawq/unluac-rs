-- regress_419_dead_temp_physical_root: HIR 保留的 dead physical-home copy 必须阻止 AST cleanup 再删除
-- unluac: expect-contains [[no_event_callable()]]
-- unluac: expect-ast-max [[local-binding]] [[17]]
-- unluac: expect-ast-count [[function]] [[9]]
-- unluac: expect-ast-count [[local-decl]] [[0]] [[@proto=8]]

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
        assert(weak.value.marker == 42)
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
    assert(global_callable == nil)
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
assert(no_event_callable == nil)
print("regress_419_dead_temp_physical_root", "OK")
