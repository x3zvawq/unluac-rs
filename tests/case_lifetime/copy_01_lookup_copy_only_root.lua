-- regress_356_lookup_copy_only_root: only the copied home crosses the collection fence
-- 原 COPY 是跨 GC 的独立 root；限制额外声明和重复 lookup，不按自动变量编号禁止它。
-- unluac: expect-ast-count [[local-decl]] [[5]]
-- unluac: expect-ast-count [[empty-local]] [[0]]
-- unluac: expect-ast-count [[call]] [[5]]
-- unluac: expect-count [[.weak.key]] [[1]]
-- unluac: expect-count [[collectgarbage("collect")]] [[2]]

local weak_values = setmetatable({}, { __mode = "v" })
local holder = { weak = weak_values }
local owner = {}
weak_values.key = owner
owner = nil

local source = holder.weak.key
local copy = source
source = nil
collectgarbage("collect")
assert(weak_values.key ~= nil)

copy = nil
collectgarbage("collect")
assert(weak_values.key == nil)
