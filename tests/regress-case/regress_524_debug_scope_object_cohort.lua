-- 同一 debug 作用域里的表与函数必须一起结束局部根的保活期。
local function make() return {} end
local weak = setmetatable({}, { __mode = "k" })
do
    local scoped = {}
    weak[scoped] = true
    local function use(value) assert(value ~= nil) end
    use(scoped)
end
collectgarbage("collect")
assert(next(weak) == nil, "debug object scope stayed alive")
-- 声明前的求值也属于窗口：callee 别名先占结果槽，调用再产生该 binding。
do
    local scoped = make()
    weak[scoped] = true
    local function use(value) assert(value ~= nil) end
    use(scoped)
end
collectgarbage("collect")
assert(next(weak) == nil, "debug call-result scope stayed alive")
print("regress_524_debug_scope_object_cohort", "closed")
