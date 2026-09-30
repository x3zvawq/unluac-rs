-- debug end 恢复寄存器复用，不能在下一条可观察 GGET 之前主动清槽。
-- unluac: expect-ast-max [[local-binding]] [[9]]
-- unluac: expect-ast-count [[function]] [[3]]
-- 匿名对象也在原覆盖前结束词法声明，避免后续 callee 与布尔实参接棒复用。
-- unluac: expect-ast-count [[do-block]] [[2]]
-- unluac: expect-ast-count [[local-function]] [[2]]
-- unluac: expect-count [[assert(]] [[5]]
-- unluac: expect-count [[regress_525_missing_gc("collect")]] [[2]]
local gc, next_key = collectgarbage, next
local env = _G
local weak = setmetatable({}, { __mode = "k" })
local observed
env.regress_525_missing_gc = nil
setmetatable(env, {
    __index = function(_, name)
        if name == "regress_525_missing_gc" then
            gc("collect")
            observed = next_key(weak) ~= nil
            assert(observed, "debug end cleared a root before global lookup")
            return gc
        end
    end,
})
do
    local scoped = {}
    weak[scoped] = true
    local function use(value) assert(value ~= nil) end
    use(scoped)
end
regress_525_missing_gc("collect")
assert(next_key(weak) == nil, "debug object outlived the following call")
local function outer_use(value)
    gc("collect")
    assert(value ~= nil and weak[value] == true, "object died inside outer call")
end
do
    local scoped = {}
    weak[scoped] = true
    outer_use(scoped)
end
regress_525_missing_gc("collect")
assert(next_key(weak) == nil, "outer-callee object outlived the following call")
setmetatable(env, nil)
print("regress_525_debug_scope_lookup_root", observed, "closed")
