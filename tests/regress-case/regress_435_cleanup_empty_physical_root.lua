-- regress_435_cleanup_empty_physical_root: an empty local clears the reused VM home before GC

local weak = setmetatable({}, { __mode = "k" })

local function make_root()
    local value = {}
    weak[value] = true
    return value
end

local function root_is_live()
    collectgarbage("collect")
    return next(weak) ~= nil
end

local function root_is_dead()
    collectgarbage("collect")
    return next(weak) == nil
end

local function clear_reused_slot(enabled)
    do
        local old = make_root()
        assert(root_is_live())
    end
    if enabled then
        local cleared
    end
    return root_is_dead()
end

assert(clear_reused_slot(true))
assert(clear_reused_slot(false))
print("regress_435_cleanup_empty_physical_root", "OK")
