-- regress_356_physical_root_copy_lifetime: a shorter copy home cannot replace the source root

local weak_values = setmetatable({}, { __mode = "v" })
local owner = {}
weak_values.key = owner

local function take()
    local value = owner
    owner = nil
    return value
end

local first = take()
local alias = first
alias = nil

collectgarbage("collect")
collectgarbage("collect")
assert(weak_values.key ~= nil)
