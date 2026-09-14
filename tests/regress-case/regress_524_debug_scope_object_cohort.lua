-- 同一 debug 作用域里的表与函数必须一起结束局部根的保活期。
-- unluac: expect-ast-min [[do-block]] [[1]] [[@debug=retained]]
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
-- 外层函数不属于本次结束的 cohort；其别名不能阻止 scoped 的 debug 边界物化。
local function outer_use(value)
    collectgarbage("collect")
    assert(value ~= nil and weak[value] == true, "object died inside outer call")
end
do
    local scoped = {}
    weak[scoped] = true
    outer_use(scoped)
end
collectgarbage("collect")
assert(next(weak) == nil, "outer-callee object survived its scope")
print("regress_524_debug_scope_object_cohort", "closed")
