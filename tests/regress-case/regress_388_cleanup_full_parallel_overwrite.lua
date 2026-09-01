-- regress_388_cleanup_full_parallel_overwrite: fixed multi-call results retain one physical root
-- per home through eventful overwrite evaluation, then release each root at its exact overwrite
-- unluac: expect-not-contains [[local value = 0, mark()]]

local calls = 0

local function pair()
    calls = calls + 1
    return {}, {}
end

local function overwrite_pair()
    local first, second = pair()
    first, second = 11, 22
    return function()
        return first, second
    end
end

local function mark()
    calls = calls + 1
end

local function overwrite_multi_initializer()
    local value = 0, mark()
    value = 33
    return function()
        return value
    end
end

local weak = setmetatable({}, { __mode = "k" })

local function rooted_pair()
    local value = {}
    weak[value] = true
    return value, false
end

local function rooted_value()
    local value = {}
    weak[value] = true
    return value
end

local function root_is_live()
    collectgarbage("collect")
    return next(weak) ~= nil
end

local function overwritten_root_is_dead()
    collectgarbage("collect")
    return next(weak) == nil
end

local function eventful_overwrite()
    local first, second = rooted_pair()
    first, second = root_is_live(), true
    local released = overwritten_root_is_dead()
    return function()
        return first, second, released
    end
end

local function eventful_scalar_overwrite()
    local value = rooted_value()
    value = root_is_live()
    local released = overwritten_root_is_dead()
    return function()
        return value, released
    end
end

local pending_weak = setmetatable({}, { __mode = "k" })

local function pending_root()
    local value = {}
    pending_weak[value] = true
    return value
end

local function pending_root_is_live()
    collectgarbage("collect")
    return next(pending_weak) ~= nil
end

local function multi_initializer_keeps_pending_root()
    local root, live = pending_root(), pending_root_is_live()
    root, live = false, live
    return live
end

local function eventless_copy_overwrite(replacement)
    local value = rooted_value()
    value = replacement
    local released = overwritten_root_is_dead()
    return value, released
end

local first, second = overwrite_pair()()
assert(first == 11 and second == 22)
assert(overwrite_multi_initializer()() == 33)
assert(calls == 2)

local scalar, scalar_released = eventful_scalar_overwrite()()
assert(scalar == true and scalar_released == true)
collectgarbage("collect")
assert(next(weak) == nil)

assert(multi_initializer_keeps_pending_root())
collectgarbage("collect")
assert(next(pending_weak) == nil)

local copied, copy_released = eventless_copy_overwrite("copy")
assert(copied == "copy" and copy_released == true)
collectgarbage("collect")
assert(next(weak) == nil)

local rooted, marker, pair_released = eventful_overwrite()()
assert(rooted == true and marker == true and pair_released == true)
collectgarbage("collect")
assert(next(weak) == nil)
