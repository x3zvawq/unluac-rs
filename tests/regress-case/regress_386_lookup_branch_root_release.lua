-- regress_386_lookup_branch_root_release: a branch overwrite releases the lookup root before a later GC fence

local weak = setmetatable({}, { __mode = "v" })
local owner = {}
weak.key = owner
owner = nil

local function run(condition)
    local root = weak.key
    if condition then
        root = true
    else
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
