-- A source debug scope must end before the next observable event, not only before return.
-- unluac: expect-ast-count [[local-binding]] [[2]]
-- unluac: expect-ast-count [[function]] [[1]]
-- unluac: expect-ast-count [[do-block]] [[1]]
local weak = setmetatable({}, { __mode = "k" })
do
    local function scoped()
        weak[debug.getinfo(1, "f").func] = true
    end
    scoped()
    assert(weak[scoped] == true)
end
collectgarbage("collect")
assert(next(weak) == nil)
print("regress_487_debug_scope_end", "closed")
