-- regress_386_allocation_branch_root_release: a branch overwrite releases an escaped allocation root before GC

local weak = setmetatable({}, { __mode = "v" })

local function run(condition)
    local value = {}
    weak.key = value
    if condition then
        value = true
    else
        value = false
    end
    collectgarbage("collect")
    collectgarbage("collect")
    return weak.key == nil
end

assert(run(true))
assert(run(false))
