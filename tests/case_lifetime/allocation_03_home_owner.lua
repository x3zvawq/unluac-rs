-- An allocation value may occupy several VM homes, but each home has its own producer and
-- overwrite transaction. Protecting every copy under the first producer retains dead roots.
-- 两个物理 home 都必须保留，不另加释放中转变量。
-- unluac: expect-ast-count [[local-binding]] [[4]]
-- unluac: expect-ast-count [[local-binding]] [[2]] [[@proto=1]]

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
