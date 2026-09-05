-- A source debug scope must end before the next observable event, not only before return.
local weak = setmetatable({}, { __mode = "k" })
do
    local function scoped()
        weak[debug.getinfo(1, "f").func] = true
    end
    scoped()
end
collectgarbage("collect")
assert(next(weak) == nil)
print("regress_487_debug_scope_end", "closed")
