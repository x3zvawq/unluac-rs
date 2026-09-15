-- An allocation value may occupy several VM homes, but each home has its own producer and
-- overwrite transaction. Protecting every copy under the first producer retains dead roots.

local weak = setmetatable({}, { __mode = "v" })

local function copied_home_dies()
    local source = {}
    local copy = source
    source = nil
    weak[1] = copy
    copy = collectgarbage
    copy("collect")
    return weak[1] == nil
end

assert(copied_home_dies())
print("regress_452_allocation_home_owner", "OK")
