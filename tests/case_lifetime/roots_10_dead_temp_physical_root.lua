-- regress_419_dead_temp_physical_root: HIR 保留的 dead physical-home copy 必须阻止 AST cleanup 再删除
-- unluac: expect-ast-count [[call]] [[1]] [[@proto=8]]
-- unluac: expect-ast-max [[local-binding]] [[22]]
-- unluac: expect-ast-count [[function]] [[11]]
-- unluac: expect-ast-count [[local-decl]] [[1]] [[@proto=8]]

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

local function global_callee_keeps_root_during_dispatch()
    no_event_callable = function()
        no_event_callable = nil
    end
    local callee = no_event_callable
    callee()
end

run()
expires_at_overwrite()
global_callee_keeps_independent_root()
global_callee_keeps_root_during_dispatch()
assert(no_event_callable == nil)

-- 全局赋值的 __newindex 可替换刚创建的闭包；callee 内也可能观察根，不能只检查调用后缀。
local environment_weak = setmetatable({}, { __mode = "v" })
local observed, dispatches = false, 0
local previous_metatable = getmetatable(_G)
collectgarbage("stop")
setmetatable(_G, {__newindex = function(environment, key, value)
    if key == "no_event_callable" then
        local callable = setmetatable({}, {__call = function()
            dispatches = dispatches + 1
            rawset(_G, "no_event_callable", nil)
            collectgarbage("restart")
            collectgarbage("collect")
            collectgarbage("collect")
            observed = environment_weak.value ~= nil
        end})
        environment_weak.value = callable
        rawset(environment, key, callable)
    else
        rawset(environment, key, value)
    end
end})
global_callee_keeps_root_during_dispatch()
setmetatable(_G, previous_metatable)
assert(observed == true and dispatches == 1, "environment replacement lost the callable root")
assert(rawget(_G, "no_event_callable") == nil)
assert(getmetatable(_G) == previous_metatable)
print("environment-callable-root", observed, dispatches)
print("regress_419_dead_temp_physical_root", "OK")
