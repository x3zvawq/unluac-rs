-- 外层捕获 cell 被 __call 清空后，callee scratch 与局部对象仍须保留原 VM 的两个 GC 时点。
local gc = collectgarbage
local weak = setmetatable({}, { __mode = "v" })
local callee
callee = setmetatable({}, {
    __call = function(self, value)
        callee = nil
        gc("collect")
        assert(weak[1] == self, "callee died during its call")
        assert(weak[2] == value, "object died inside its scope")
    end,
})
weak[1] = callee
local env = _G
env.regress_533_missing_gc = nil
setmetatable(env, { __index = function(_, key)
    if key == "regress_533_missing_gc" then
        gc("collect")
        assert(weak[1] ~= nil, "debug end cleared callee before lookup")
        assert(weak[2] ~= nil, "debug end cleared scoped object before lookup")
        return gc
    end
end })
do
    local scoped = {}
    weak[2] = scoped
    callee(scoped)
end
regress_533_missing_gc("collect")
assert(weak[1] == nil and weak[2] == nil, "object survived the following call")
setmetatable(env, nil)
print("regress_533_debug_scope_mutable_callee", "closed")
