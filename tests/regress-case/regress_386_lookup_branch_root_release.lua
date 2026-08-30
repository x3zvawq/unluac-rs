-- regress_386_lookup_branch_root_release: a branch overwrite releases the lookup root before a later GC fence

local weak = setmetatable({}, { __mode = "v" })
local owner = {}
weak.key = owner
owner = nil

local function run(condition)
    local root = weak.key
    if condition then
        collectgarbage("collect")
        assert(weak.key ~= nil)
        root = true
    else
        collectgarbage("collect")
        assert(weak.key ~= nil)
        root = false
    end
    collectgarbage("collect")
    collectgarbage("collect")
    return weak.key == nil
end

assert(run(true))

owner = {}
weak.key = owner
owner = nil
assert(run(false))

local function release_before_terminal(condition)
    local root = weak.key
    local released
    if condition then
        root = nil
        collectgarbage("collect")
        collectgarbage("collect")
        released = weak.key == nil
        root = true
    else
        root = nil
        collectgarbage("collect")
        collectgarbage("collect")
        released = weak.key == nil
        root = false
    end
    return released
end

owner = {}
weak.key = owner
owner = nil
assert(release_before_terminal(true))

owner = {}
weak.key = owner
owner = nil
assert(release_before_terminal(false))

local successor_weak = setmetatable({}, { __mode = "k" })

local function make_successor()
    collectgarbage("collect")
    assert(weak.key ~= nil)
    local value = {}
    successor_weak[value] = true
    return value
end

local function replace_with_successor(condition)
    local root = weak.key
    if condition then
        root = make_successor()
    else
        root = make_successor()
    end
    collectgarbage("collect")
    assert(next(successor_weak) ~= nil)
    return root
end

owner = {}
weak.key = owner
owner = nil
assert(replace_with_successor(true) ~= nil)

collectgarbage("collect")
assert(next(successor_weak) == nil)

owner = {}
weak.key = owner
owner = nil
assert(replace_with_successor(false) ~= nil)
